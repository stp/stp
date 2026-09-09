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

#include "stp/UninterpretedFunctions/UFRefinement.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolver.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "extlib-constbv/constantbv.h"
#include <algorithm>
#include <iostream>
#include <map>
#include <set>
#include <sstream>

namespace stp
{

namespace
{

struct EqualityKey
{
  ASTNode left;
  ASTNode right;
  SourceSort sort;

  bool operator<(const EqualityKey& other) const
  {
    if (sort.kind() != other.sort.kind())
      return static_cast<int>(sort.kind()) <
             static_cast<int>(other.sort.kind());
    // Bool is the one admitted sort with no carrier width to compare;
    // everything else is separated by its packed width within a kind.
    if (sort.kind() != SourceSort::Kind::Bool &&
        sort.packedWidth() != other.sort.packedWidth())
      return sort.packedWidth() < other.sort.packedWidth();
    if (left != other.left)
      return left < other.left;
    return right < other.right;
  }
};

EqualityKey equalityKey(ASTNode left, ASTNode right, const SourceSort& sort)
{
  if (right < left)
    std::swap(left, right);
  EqualityKey key;
  key.left = left;
  key.right = right;
  key.sort = sort;
  return key;
}

struct PersistentScopeKey
{
  uint64_t epoch = 0;
  uint64_t backendGeneration = 0;
  uint64_t block = 0;

  bool operator<(const PersistentScopeKey& other) const
  {
    if (epoch != other.epoch)
      return epoch < other.epoch;
    return backendGeneration != other.backendGeneration
               ? backendGeneration < other.backendGeneration
               : block < other.block;
  }
};

class CounterExampleCandidate final : public UFScalarCandidate
{
public:
  CounterExampleCandidate(AbsRefine_CounterExample& ce,
                          const UFContext& context, uint64_t version)
      : ce_(ce), context_(context), version_(version)
  {
  }

  uint64_t version() const override { return version_; }

  bool read(const ASTNode& scalar, const SourceSort& expected,
            UFConcreteValue& value,
            std::string& diagnostic) const override
  {
    if (scalar.IsNull() || scalar.GetKind() != SYMBOL ||
        scalar.GetSourceSort() != expected)
    {
      diagnostic = "UF adapter was asked to read a non-symbol or wrong-sort "
                   "candidate scalar";
      return false;
    }
    if (!context_.isSolveScalar(scalar))
    {
      diagnostic = "UF checker scalar was not registered as a SAT candidate "
                   "authority";
      return false;
    }
    ASTNode assigned = ce_.LookupAssignedValue(scalar);
    if (assigned.IsNull() || !assigned.isConstant())
    {
      // Every symbolic argument leaf, introduced actual name and result has
      // one authority: the complete mapping registered in the current SAT
      // backend.  Never fall back through SolverMap/model evaluation here;
      // doing so would let a lemma encode one value while the checker read
      // another.
      diagnostic = "UF solve scalar has no direct up-front SAT assignment";
      return false;
    }
    return UFConcreteValue::fromConstant(assigned, expected, value,
                                         diagnostic);
  }

private:
  AbsRefine_CounterExample& ce_;
  const UFContext& context_;
  const uint64_t version_;
};

// One validated congruence clause waiting to be installed, with the
// declaration whose candidate it refutes: that name is what the `-s` trace
// prints when the clause goes in.
struct PendingLemma
{
  UFAbstractLemma lemma;
  const UFDecl* declaration = NULL;
};

// The packed carrier width of a solved sort; defined below with the rest of
// the scalar reading, and needed here to group by carrier.
unsigned scalarWidth(const SourceSort& sort);

// The distinct argument terms of each lowering sort, in node order.
//
// Grouped by the carrier the encoder actually compares -- a kind and a width
// -- because two sorts that share both are compared bit for bit the same way.
// The propagator's atom pool and the decision of whether there can be one are
// the same question asked twice, so they ask it here.
typedef std::map<std::pair<int, unsigned>,
                 std::pair<SourceSort, std::vector<ASTNode>>>
    ArgumentTermsBySort;

ArgumentTermsBySort argumentTermsBySort(const LoweredApplicationView& view)
{
  ArgumentTermsBySort out;
  for (const LoweredApplicationRecord& record : view.applications)
  {
    if (!record.observableArguments || record.declaration == NULL)
      continue;
    const std::vector<SourceSort>& domain =
        record.declaration->signature().domain();
    for (size_t i = 0; i < record.namedActuals.size() && i < domain.size();
         ++i)
    {
      const SourceSort sort = UFSignature::loweringSort(domain[i]);
      const std::pair<int, unsigned> key(static_cast<int>(sort.kind()),
                                         scalarWidth(sort));
      std::pair<SourceSort, std::vector<ASTNode>>& group = out[key];
      group.first = sort;
      group.second.push_back(record.namedActuals[i]);
    }
  }
  for (ArgumentTermsBySort::iterator it = out.begin(); it != out.end(); ++it)
  {
    std::vector<ASTNode>& terms = it->second.second;
    // Node order, so the same query mints the same pool.
    std::sort(terms.begin(), terms.end(),
              [](const ASTNode& left, const ASTNode& right)
              { return left.GetNodeNum() < right.GetNodeNum(); });
    terms.erase(std::unique(terms.begin(), terms.end()), terms.end());
  }
  return out;
}

// Whether any sort has a pool the cap admits. Asked once per query, before
// the first lemma, because the answer decides whether this query's equality
// atoms are worth keeping out of variable elimination -- and that has to be
// decided while they are still whole.
//
// It is not free to get wrong in either direction. Protecting the atoms of a
// query the closure will never serve measured 7.8 s -> 8.8 s on 1462.smt2,
// which has 81 lemmas and not one sort the cap admits.
bool propagatorPoolPossible(const LoweredApplicationView& view, unsigned cap)
{
  if (cap < 2)
    return false;
  const ArgumentTermsBySort groups = argumentTermsBySort(view);
  for (ArgumentTermsBySort::const_iterator it = groups.begin();
       it != groups.end(); ++it)
    if (it->second.second.size() >= 2 && it->second.second.size() <= cap)
      return true;
  return false;
}

struct MutableAdapterState
{
  explicit MutableAdapterState(STPMgr* manager_) : manager(manager_) {}

  STPMgr* manager;
  const LoweredApplicationView* view = NULL;
  UFCheckPlan checkPlan;
  std::string checkPlanDiagnostic;
  // Every lemma the last refuted candidate produced, in the checker's
  // deterministic conflict order. Empty exactly when no candidate is pending.
  std::vector<PendingLemma> pending;
  bool certified = false;
  UFFunctionModelSeedSet seed;
  std::map<ASTNode, UFConcreteValue> handleValues;
  std::string diagnostic;
  uint64_t nextCandidateVersion = 0;
  uint64_t emittedLemmaCount = 0;
  // Whether this query can have an atom pool at all, decided at beginView.
  bool propagatorPoolPossible = false;

  void clearRound()
  {
    pending.clear();
    certified = false;
    seed = UFFunctionModelSeedSet();
    handleValues.clear();
    diagnostic.clear();
  }

  void clearActive()
  {
    clearRound();
    view = NULL;
    checkPlan = UFCheckPlan();
    checkPlanDiagnostic.clear();
  }

  void beginView(const LoweredApplicationView* nextView)
  {
    clearRound();
    view = nextView;
    checkPlan = UFCheckPlan();
    checkPlanDiagnostic.clear();
    propagatorPoolPossible = false;
    if (view == NULL || !view->active())
      return;
    propagatorPoolPossible =
        manager->UserFlags.uf_propagator &&
        stp::propagatorPoolPossible(*view,
                                    manager->UserFlags.uf_propagator_pool);
    UFContext* context = manager->getUFContextIfAny();
    if (context == NULL)
    {
      checkPlanDiagnostic =
          "UF adapter has an active view but no UF context";
      return;
    }
    checkPlan = UFChecker::validate(context->activeDeclarations(), *view);
    if (!checkPlan.valid())
      checkPlanDiagnostic = checkPlan.diagnostic();
  }
};

UFCandidateOutcome checkOneCandidate(
    MutableAdapterState& state,
    AbsRefine_CounterExample& counterexample)
{
  state.clearRound();
  if (state.view == NULL || !state.view->active())
    return UFCandidateOutcome::Skipped;
  if (!state.checkPlan.valid())
  {
    state.diagnostic = state.checkPlanDiagnostic.empty()
                           ? "UF adapter has no validated checker plan"
                           : state.checkPlanDiagnostic;
    return UFCandidateOutcome::InternalError;
  }
  UFContext* context = state.manager->getUFContextIfAny();
  if (context == NULL)
  {
    state.diagnostic = "UF adapter has an active view but no UF context";
    return UFCandidateOutcome::InternalError;
  }

  const uint64_t version = ++state.nextCandidateVersion;
  CounterExampleCandidate candidate(counterexample, *context, version);
  UFCheckResult result = UFChecker::check(
      state.checkPlan, candidate,
      state.manager->UserFlags.uf_lemmas_per_round);
  if (result.status == UFCheckResult::Status::InternalError)
  {
    state.diagnostic = result.diagnostic;
    return UFCandidateOutcome::InternalError;
  }
  if (result.hasConflict())
  {
    if (result.conflicts.empty())
    {
      state.diagnostic = "UFCHK reported a conflict with no certificate";
      return UFCandidateOutcome::InternalError;
    }
    // Each conflict is refuted by the same unchanged candidate, so all of
    // them are built and validated here, before the encoder is allowed to
    // touch SAT at all. A single failure abandons the whole batch.
    state.pending.reserve(result.conflicts.size());
    for (const UFCongruenceConflict& conflict : result.conflicts)
    {
      PendingLemma entry;
      if (!UFLemmaOracle::buildAndValidate(conflict, entry.lemma,
                                           state.diagnostic))
      {
        state.pending.clear();
        return UFCandidateOutcome::InternalError;
      }
      if (entry.lemma.candidateVersion != version)
      {
        state.pending.clear();
        state.diagnostic = "UF lemma retained the wrong candidate version";
        return UFCandidateOutcome::InternalError;
      }
      entry.declaration = conflict.declaration;
      state.pending.push_back(entry);
    }
    return UFCandidateOutcome::Conflict;
  }

  if (!result.consistent() || result.modelSeed.candidateVersion != version)
  {
    state.diagnostic = "UF checker returned a malformed consistency seed";
    return UFCandidateOutcome::InternalError;
  }

  // Preserve every active durable handle, including duplicate applications
  // omitted from the finite table's one representative per concrete tuple.
  for (const LoweredApplicationRecord& record : state.view->applications)
  {
    UFConcreteValue value;
    if (!candidate.read(record.resultSymbol,
                        record.resultSymbol.GetSourceSort(),
                        value, state.diagnostic))
      return UFCandidateOutcome::InternalError;
    state.handleValues.insert(std::make_pair(record.durableHandle, value));
  }
  if (candidate.version() != version)
  {
    state.diagnostic = "UF candidate changed while retaining certified "
                       "handle values";
    return UFCandidateOutcome::InternalError;
  }
  state.seed = result.modelSeed;
  state.certified = true;
  return UFCandidateOutcome::Consistent;
}

// As in UFLemma: CNF leaves live at the lowering sort, where FloatingPoint
// never appears.
bool supportedSort(const SourceSort& sort)
{
  return UFSignature::isSupportedSort(sort) &&
         sort.kind() != SourceSort::Kind::FloatingPoint;
}

// How many SAT bits one scalar of this sort occupies. Bool is a single
// literal; everything else is its packed carrier, which is exactly what the
// solve-scalar registrar in ToSATAIG allocates from GetValueWidth().
unsigned scalarWidth(const SourceSort& sort)
{
  return sort.kind() == SourceSort::Kind::Bool ? 1 : sort.packedWidth();
}

const char* validateLeaf(
    const ASTNode& leaf, const SourceSort& sort,
    const ToSATBase::ASTNodeToSATVar& bindings)
{
  if (!supportedSort(sort) || leaf.IsNull() || leaf.GetSourceSort() != sort)
    return "UF CNF leaf has the wrong SourceSort";
  if (leaf.isConstant())
  {
    if (sort.kind() == SourceSort::Kind::Bool)
      return leaf.GetKind() == TRUE || leaf.GetKind() == FALSE
                 ? NULL
                 : "UF CNF Boolean constant is malformed";
    return leaf.GetKind() == BVCONST &&
                   leaf.GetValueWidth() == sort.packedWidth()
               ? NULL
               : "UF CNF scalar constant is malformed";
  }
  if (leaf.GetKind() != SYMBOL)
    return "UF CNF leaf is neither a constant nor a symbol";
  const ToSATBase::ASTNodeToSATVar::const_iterator found = bindings.find(leaf);
  if (found == bindings.end())
    return "UF CNF leaf was not registered before the first candidate";
  if (found->second.size() != scalarWidth(sort))
    return "UF CNF leaf has a wrong-width SAT mapping";
  for (const unsigned variable : found->second)
    if (variable == ~((unsigned)0))
      return "UF CNF leaf has an unencoded SAT bit";
  return NULL;
}

void validateLemmaBeforeMutation(
    const UFAbstractLemma& lemma,
    const ToSATBase::ASTNodeToSATVar& bindings, SATSolver& solver,
    int guardLiteral)
{
  std::vector<const UFEqualityAtom*> atoms;
  atoms.reserve(lemma.premise.size() + 1);
  for (const UFEqualityAtom& atom : lemma.premise)
    atoms.push_back(&atom);
  atoms.push_back(&lemma.conclusion);
  for (const UFEqualityAtom* atom : atoms)
  {
    const char* reason = validateLeaf(atom->left, atom->sort, bindings);
    if (reason != NULL)
      FatalError(reason, atom->left);
    reason = validateLeaf(atom->right, atom->sort, bindings);
    if (reason != NULL)
      FatalError(reason, atom->right);
  }
  // Backends expose different variable bases through this historical API
  // (CaDiCaL is one-based, MiniSat-family wrappers are zero-based), so nVars
  // cannot portably validate the upper bound. The exact-stack encoder handed
  // us a nonnegative literal obtained from its own live AIG binding; retain
  // that provenance check without inventing a backend-specific comparison.
  (void)solver;
  if (guardLiteral < -1)
    FatalError("UF persistent block guard is malformed");
  const std::vector<bool> premises(lemma.premise.size(), true);
  if (lemma.evaluate(false, premises))
    FatalError("UF abstract lemma does not reject its triggering candidate");
}

struct BitOperand
{
  bool constant = false;
  bool value = false;
  unsigned variable = 0;
};

BitOperand bitOperand(const ASTNode& leaf, const SourceSort& sort,
                      unsigned bit,
                      const ToSATBase::ASTNodeToSATVar& bindings)
{
  BitOperand result;
  if (!leaf.isConstant())
  {
    result.variable = bindings.find(leaf)->second[bit];
    return result;
  }
  result.constant = true;
  if (sort.kind() == SourceSort::Kind::Bool)
    result.value = leaf.GetKind() == TRUE;
  else
    result.value =
        CONSTANTBV::BitVector_bit_test(leaf.GetBVConst(), bit) != 0;
  return result;
}

struct ClauseTerm
{
  bool constant = false;
  bool value = false;
  int literal = -1;

  static ClauseTerm constantValue(bool value_)
  {
    ClauseTerm term;
    term.constant = true;
    term.value = value_;
    return term;
  }
  static ClauseTerm satLiteral(int literal_)
  {
    ClauseTerm term;
    term.literal = literal_;
    return term;
  }
};

ClauseTerm negate(ClauseTerm term)
{
  if (term.constant)
    term.value = !term.value;
  else
    term.literal ^= 1;
  return term;
}

ClauseTerm exclusionLiteral(const BitOperand& operand, bool assignment)
{
  if (operand.constant)
    return ClauseTerm::constantValue(operand.value != assignment);
  return ClauseTerm::satLiteral(
      static_cast<int>(2 * operand.variable + (assignment ? 1 : 0)));
}

void addGuardedClause(SATSolver& solver,
                      const std::vector<ClauseTerm>& terms,
                      int guardLiteral)
{
  SATSolver::vec_literals clause;
  for (const ClauseTerm& term : terms)
  {
    if (term.constant)
    {
      if (term.value)
        return; // tautology
      continue;
    }
    clause.push(SATSolver::mkLit(term.literal >> 1,
                                 (term.literal & 1) != 0));
  }
  if (guardLiteral >= 0)
    clause.push(SATSolver::mkLit(guardLiteral >> 1,
                                 (guardLiteral & 1) != 0));
  solver.addClause(clause);
}

// How the equality literal is about to be used in the lemma clause. A premise
// appears negated and a conclusion positive, and each direction of the
// definition is needed by exactly one of them:
//
//   conclusion   ... v q      needs  q -> equality
//   premise      ... v ~q     needs  equality -> q
//
// Emitting only the needed half is sound because the other direction only
// ever constrains the helper in a polarity no clause mentions: the solver may
// set the helper freely there, and every clause that names it stays
// satisfied for the same reason it was before. The halves are tracked per
// cached atom, so an atom later used in the opposite polarity is completed
// then rather than being defined twice.
enum class Polarity
{
  Positive, // the literal appears positively: define q -> equality
  Negative  // the literal appears negated: define equality -> q
};

// One bit of an equality, as it was encoded. `allocated` distinguishes a
// fresh XNOR helper, which has to be defined, from a literal that already is
// the bit equality (a constant operand collapses to the other operand's
// literal) and needs no clauses at all.
struct BitHelper
{
  int literal = -1;
  bool allocated = false;
  BitOperand left;
  BitOperand right;
};

// One cached equality atom: its literal, the per-bit helpers behind it, and
// which halves of the definition have been emitted so far.
struct CachedEquality
{
  int literal = -1;
  std::vector<BitHelper> bits;
  bool aggregateAllocated = false;
  bool positiveDefined = false;
  bool negativeDefined = false;
};

void defineBitHelper(SATSolver& solver, const BitHelper& helper,
                     Polarity polarity, int guardLiteral)
{
  if (!helper.allocated)
    return;
  const unsigned q = static_cast<unsigned>(helper.literal >> 1);
  // The clause set below blocks each assignment that would falsify the
  // definition. Those with q true are exactly q -> (l = r); those with q
  // false are exactly (l = r) -> q.
  const bool wantQTrue = polarity == Polarity::Positive;
  for (unsigned lv = 0; lv < 2; ++lv)
    for (unsigned rv = 0; rv < 2; ++rv)
    {
      const unsigned qv = (lv == rv) ? 0u : 1u;
      if ((qv != 0) != wantQTrue)
        continue;
      std::vector<ClauseTerm> clause;
      clause.push_back(exclusionLiteral(helper.left, lv != 0));
      clause.push_back(exclusionLiteral(helper.right, rv != 0));
      clause.push_back(ClauseTerm::satLiteral(
          static_cast<int>(2 * q + (qv != 0 ? 1 : 0))));
      addGuardedClause(solver, clause, guardLiteral);
    }
}

void defineEquality(SATSolver& solver, CachedEquality& cached,
                    Polarity polarity, int guardLiteral)
{
  bool& done = polarity == Polarity::Positive ? cached.positiveDefined
                                              : cached.negativeDefined;
  if (done)
    return;
  done = true;
  for (const BitHelper& helper : cached.bits)
    defineBitHelper(solver, helper, polarity, guardLiteral);
  if (!cached.aggregateAllocated)
    return;
  if (polarity == Polarity::Positive)
  {
    // q -> every bit equality
    for (const BitHelper& helper : cached.bits)
    {
      std::vector<ClauseTerm> clause;
      clause.push_back(ClauseTerm::satLiteral(cached.literal ^ 1));
      clause.push_back(ClauseTerm::satLiteral(helper.literal));
      addGuardedClause(solver, clause, guardLiteral);
    }
    return;
  }
  // every bit equality -> q
  std::vector<ClauseTerm> reverse;
  reverse.push_back(ClauseTerm::satLiteral(cached.literal));
  for (const BitHelper& helper : cached.bits)
    reverse.push_back(ClauseTerm::satLiteral(helper.literal ^ 1));
  addGuardedClause(solver, reverse, guardLiteral);
}

// Both halves of an atom's definition. The lemma encoder writes only the one
// its clause needs; a caller that reads the atom in the other direction --
// the congruence propagator, whose chains of asserted equalities have to
// imply the equalities themselves -- has to ask for the rest.
void completeEquality(SATSolver& solver, CachedEquality& cached)
{
  defineEquality(solver, cached, Polarity::Positive, -1);
  defineEquality(solver, cached, Polarity::Negative, -1);
}

// Fold constants and SAT aliases before allocating an XNOR helper; the helper
// itself is left undefined here and is given whichever half the use needs.
BitHelper bitEquality(SATSolver& solver, const BitOperand& left,
                      const BitOperand& right, bool& constantResult,
                      bool& constantValue)
{
  BitHelper helper;
  helper.left = left;
  helper.right = right;
  constantResult = false;
  if (left.constant && right.constant)
  {
    constantResult = true;
    constantValue = left.value == right.value;
    return helper;
  }
  if (!left.constant && !right.constant && left.variable == right.variable)
  {
    constantResult = true;
    constantValue = true;
    return helper;
  }
  if (left.constant || right.constant)
  {
    const BitOperand& constant = left.constant ? left : right;
    const BitOperand& symbol = left.constant ? right : left;
    helper.literal =
        static_cast<int>(2 * symbol.variable + (constant.value ? 0 : 1));
    return helper;
  }

  const unsigned q = solver.newVar();
  solver.setFrozen(q);
  helper.literal = static_cast<int>(2 * q);
  helper.allocated = true;
  return helper;
}

// `protectAtoms` keeps a newly minted atom out of the backend's variable
// elimination. Only wanted when the congruence propagator may later observe
// it: an observation is only accepted on a variable that has not been
// eliminated, and the restore that would make an eliminated one whole again
// runs inside the next solve, which is after the last moment it could be
// observed. Off, the encoder's variables stay as eliminable as every other
// refinement variable, which is what they were before.
ClauseTerm equalityTerm(SATSolver& solver,
                        const ToSATBase::ASTNodeToSATVar& bindings,
                        const UFEqualityAtom& atom, Polarity polarity,
                        int guardLiteral,
                        std::map<EqualityKey, CachedEquality>& cache,
                        bool protectAtoms)
{
  const EqualityKey key = equalityKey(atom.left, atom.right, atom.sort);
  if (key.left == key.right)
    return ClauseTerm::constantValue(true);
  if (key.left.isConstant() && key.right.isConstant())
  {
    const bool equal = atom.sort.kind() == SourceSort::Kind::Bool
                           ? key.left.GetKind() == key.right.GetKind()
                           : constantsSameBits(key.left, key.right);
    return ClauseTerm::constantValue(equal);
  }
  const std::map<EqualityKey, CachedEquality>::iterator hit = cache.find(key);
  if (hit != cache.end())
  {
    defineEquality(solver, hit->second, polarity, guardLiteral);
    return ClauseTerm::satLiteral(hit->second.literal);
  }

  const unsigned width = scalarWidth(atom.sort);
  CachedEquality cached;
  cached.bits.reserve(width);
  for (unsigned bit = 0; bit < width; ++bit)
  {
    const BitOperand left = bitOperand(key.left, atom.sort, bit, bindings);
    const BitOperand right = bitOperand(key.right, atom.sort, bit, bindings);
    bool constantResult = false;
    bool constantValue = false;
    const BitHelper helper =
        bitEquality(solver, left, right, constantResult, constantValue);
    if (constantResult)
    {
      // A bit that can never agree makes the whole equality false; one that
      // always agrees contributes nothing. Neither needs a helper, and a
      // false one abandons the atom before anything is cached -- any helper
      // already allocated for an earlier bit simply stays undefined and
      // unused.
      if (!constantValue)
        return ClauseTerm::constantValue(false);
      continue;
    }
    cached.bits.push_back(helper);
  }

  if (cached.bits.empty())
    return ClauseTerm::constantValue(true);

  cached.literal = cached.bits[0].literal;
  if (cached.bits.size() > 1)
  {
    const unsigned q = solver.newVar();
    solver.setFrozen(q);
    cached.literal = static_cast<int>(2 * q);
    cached.aggregateAllocated = true;
  }
  const std::map<EqualityKey, CachedEquality>::iterator inserted =
      cache.insert(std::make_pair(key, cached)).first;
  if (protectAtoms)
    solver.protectFromElimination(
        (unsigned)(inserted->second.literal >> 1));
  defineEquality(solver, inserted->second, polarity, guardLiteral);
  return ClauseTerm::satLiteral(inserted->second.literal);
}

// The atom for one term pair, with both halves of its definition, as the
// literal that carries it -- or -1 when the pair folds to a constant and
// needs no atom at all.
int mintEquality(SATSolver& solver,
                 const ToSATBase::ASTNodeToSATVar& bindings,
                 const UFEqualityAtom& atom,
                 std::map<EqualityKey, CachedEquality>& cache)
{
  const ClauseTerm term = equalityTerm(solver, bindings, atom,
                                       Polarity::Negative, -1, cache, true);
  if (term.constant)
    return -1;
  const std::map<EqualityKey, CachedEquality>::iterator hit =
      cache.find(equalityKey(atom.left, atom.right, atom.sort));
  if (hit == cache.end())
    return -1;
  completeEquality(solver, hit->second);
  return hit->second.literal;
}

void encodeOneLemma(MutableAdapterState& state, const PendingLemma& entry,
                    SATSolver& solver,
                    ToSATBase::ASTNodeToSATVar& bindings, int guardLiteral,
                    std::map<EqualityKey, CachedEquality>& cache,
                    bool protectAtoms)
{
  std::vector<ClauseTerm> body;
  body.reserve(entry.lemma.premise.size() + 1);
  for (const UFEqualityAtom& premise : entry.lemma.premise)
  {
    const ClauseTerm equality =
        equalityTerm(solver, bindings, premise, Polarity::Negative,
                     guardLiteral, cache, protectAtoms);
    if (equality.constant)
    {
      if (!equality.value)
        FatalError("UF lemma premise is structurally false", premise.left);
      continue;
    }
    body.push_back(negate(equality));
  }
  const ClauseTerm conclusion =
      equalityTerm(solver, bindings, entry.lemma.conclusion,
                   Polarity::Positive, guardLiteral, cache, protectAtoms);
  if (conclusion.constant)
  {
    if (conclusion.value)
      FatalError("UF conflicting conclusion is structurally true",
                 entry.lemma.conclusion.left);
  }
  else
    body.push_back(conclusion);
  addGuardedClause(solver, body, guardLiteral);
  state.emittedLemmaCount++;
  state.manager->UserFlags.coverage.uf_constraints_installed++;
  // Observability under -s: every lemma that reaches this path was earned by
  // a refuted candidate; constraints installed eagerly during lowering do not
  // pass through here. One line per installation names the declaration and
  // the host: a batch lemma is query-local, while a persistent one carries the
  // exact-stack block guard.
  if (state.manager->UserFlags.stats_flag)
    std::cerr << "UF: installed congruence lemma " << state.emittedLemmaCount
              << " for "
              << (entry.declaration != NULL ? entry.declaration->name()
                                            : std::string("<unknown>"))
              << (guardLiteral >= 0 ? " (block guarded)" : " (query local)")
              << std::endl;
}

void encodeLemmas(MutableAdapterState& state, SATSolver& solver,
                  ToSATBase* tosat, int guardLiteral,
                  std::map<EqualityKey, CachedEquality>& cache)
{
  if (state.pending.empty() || tosat == NULL)
    FatalError("UF lemma encoding began without a pending certificate");
  ToSATBase::ASTNodeToSATVar& bindings = tosat->SATVar_to_SymbolIndexMap();

  // Validate the whole batch before any of it mutates SAT. Splitting the two
  // loops is what keeps the batch as atomic as a single clause was: a lemma
  // the encoder would reject cannot leave earlier clauses of the same
  // candidate behind.
  for (const PendingLemma& entry : state.pending)
    validateLemmaBeforeMutation(entry.lemma, bindings, solver, guardLiteral);

  // Only the batch adapter can connect a theory to its backend -- a
  // persistent block's clauses are guarded and its solver outlives the
  // query -- so only its atoms are worth protecting.
  const bool protectAtoms = guardLiteral < 0 && state.propagatorPoolPossible;
  for (const PendingLemma& entry : state.pending)
    encodeOneLemma(state, entry, solver, bindings, guardLiteral, cache,
                   protectAtoms);

  // Some backends detect at insertion time that a validated blocking clause
  // closes the entire instance. That is a normal refinement outcome: leave the
  // solver in its UNSAT state so the coordinator's next solve can certify it,
  // rather than misclassifying progress as an internal error. The rest of the
  // batch is still installed -- every clause is a theory consequence, so
  // adding one to an already-closed instance changes nothing.
  if (state.manager->UserFlags.stats_flag && state.pending.size() > 1)
    std::cerr << "UF: candidate refuted by " << state.pending.size()
              << " congruence lemmas" << std::endl;
  state.pending.clear();
}

bool lookupCertified(const MutableAdapterState& state,
                     const ASTNode& durableHandle, UFConcreteValue& value)
{
  if (!state.certified)
    return false;
  std::map<ASTNode, UFConcreteValue>::const_iterator found =
      state.handleValues.find(durableHandle);
  // A handle pre-lowering rewrote was certified under its image.
  if (found == state.handleValues.end() && state.view != NULL)
  {
    const ASTNodeMap::const_iterator alias =
        state.view->handleAliases.find(durableHandle);
    if (alias != state.view->handleAliases.end())
      found = state.handleValues.find(alias->second);
  }
  if (found == state.handleValues.end())
    return false;
  value = found->second;
  return true;
}

} // namespace

class UFBatchAdapter::Impl
{
public:
  explicit Impl(STPMgr* manager) : state(manager) {}
  MutableAdapterState state;
  std::map<EqualityKey, CachedEquality> equalityCache;
  // Connected once, then owned for the life of the query: the backend holds
  // a pointer to it and its own trail is the theory's context.
  std::unique_ptr<UFCongruencePropagator> propagator;
};

UFBatchAdapter::UFBatchAdapter(STPMgr* manager) : impl_(new Impl(manager))
{
  assert(manager != NULL);
}
UFBatchAdapter::~UFBatchAdapter() = default;
void UFBatchAdapter::beginQuery(const LoweredApplicationView* view)
{
  clear();
  impl_->state.beginView(view);
}
// Every atom in the query's equality cache, with both halves of its
// definition, handed to the closure along with the applications it may find
// congruent.
//
// The atoms are the ones the refinement loop has already minted, so the
// clauses added here are the missing half of a definition that is already
// paid for -- not a new pool. That is the whole economy of the thing: an
// eager pool over the same terms costs O(terms^2) atom definitions and
// O(terms^3) triples whether or not the search ever needs them, and on the
// queries that are refuted in two rounds it is an order of magnitude more
// clauses than the query itself.
bool UFBatchAdapter::installCongruencePropagator(SATSolver& solver,
                                                 ToSATBase* tosat)
{
  STPMgr* const manager = impl_->state.manager;
  if (impl_->propagator || tosat == NULL || impl_->state.view == NULL)
    return false;
  if (!manager->UserFlags.uf_propagator)
    return false;
  if (impl_->state.emittedLemmaCount < manager->UserFlags.uf_propagator_after)
    return false;
  if (!impl_->state.propagatorPoolPossible)
    return false;
  if (!solver.supportsTheoryPropagation())
    return false;

  std::unique_ptr<UFCongruencePropagator> propagator(
      new UFCongruencePropagator());

  // Every pair of argument terms of a sort the cap admits, so that the
  // closure has a graph dense enough to reason over.
  //
  // The refinement loop's own atoms are the pairs some candidate collided
  // on, and transitivity needs all three sides of a triangle to exist before
  // it can say anything -- 103 atoms over 209 terms is not a graph, it is a
  // scattering of edges. Pairs go by lowering sort rather than by
  // declaration and position: applications of different declarations still
  // share the terms their arguments name, and the sort is what decides
  // whether an equality between two of them is well formed at all.
  //
  // The cost is the O(n^2) atom definitions, which the cap bounds. The
  // O(n^3) transitivity triples an eager encoding needs beside them are
  // exactly what the closure is here to replace.
  const unsigned poolCap = manager->UserFlags.uf_propagator_pool;
  const ToSATBase::ASTNodeToSATVar& bindings =
      tosat->SATVar_to_SymbolIndexMap();
  const ArgumentTermsBySort groups =
      argumentTermsBySort(*impl_->state.view);
  for (ArgumentTermsBySort::const_iterator it = groups.begin();
       it != groups.end(); ++it)
  {
    const std::vector<ASTNode>& terms = it->second.second;
    if (terms.size() < 2 || terms.size() > poolCap)
      continue;
    for (size_t left = 0; left < terms.size(); ++left)
      for (size_t right = left + 1; right < terms.size(); ++right)
      {
        UFEqualityAtom pair;
        pair.left = terms[left];
        pair.right = terms[right];
        pair.sort = it->second.first;
        mintEquality(solver, bindings, pair, impl_->equalityCache);
      }
  }

  for (std::map<EqualityKey, CachedEquality>::iterator it =
           impl_->equalityCache.begin();
       it != impl_->equalityCache.end(); ++it)
  {
    CachedEquality& cached = it->second;
    if (cached.literal < 0)
      continue;
    // Both halves, whichever the lemmas happened to need. A chain of atoms
    // that are merely implied by their equalities proves nothing: the
    // closure reads an atom in the direction the lemmas never did.
    completeEquality(solver, cached);
    const unsigned left = propagator->term(it->first.left);
    const unsigned right = propagator->term(it->first.right);
    propagator->addAtom(left, right, (uint32_t)cached.literal);
  }

  if (manager->UserFlags.uf_propagator_congruence)
  {
    const ToSATBase::ASTNodeToSATVar& bindings =
        tosat->SATVar_to_SymbolIndexMap();
    for (const LoweredApplicationRecord& record : impl_->state.view->applications)
    {
      // An application whose arguments the lowering declined to name is
      // interpreted by a constant, and has no argument terms to close over.
      if (!record.observableArguments || record.resultSymbol.IsNull())
        continue;
      const ToSATBase::ASTNodeToSATVar::const_iterator result =
          bindings.find(record.resultSymbol);
      if (result == bindings.end() || result->second.empty())
        continue;

      std::vector<unsigned> resultBits;
      resultBits.reserve(result->second.size());
      bool complete = true;
      for (unsigned bit : result->second)
      {
        if (bit == ~((unsigned)0))
        {
          complete = false; // a bit that reached no variable: nothing to watch
          break;
        }
        resultBits.push_back(bit);
      }
      if (!complete)
        continue;

      std::vector<unsigned> arguments;
      arguments.reserve(record.namedActuals.size());
      for (const ASTNode& actual : record.namedActuals)
        arguments.push_back(propagator->term(actual));
      propagator->addApplication(record.declaration, arguments, resultBits);
    }
  }

  propagator->freeze(solver.nVars());
  if (!propagator->worthConnecting())
    return false;
  if (!solver.connectTheoryPropagator(propagator.get()))
    return false;
  for (unsigned var : propagator->observedVariables())
    solver.observeVariable(var);

  if (manager->UserFlags.stats_flag)
    std::cerr << "UF: congruence propagator connected after "
              << impl_->state.emittedLemmaCount << " lemmas over "
              << propagator->termCount() << " terms, "
              << propagator->atomCount() << " equality atoms and "
              << propagator->applicationCount() << " applications ("
              << propagator->observedVariables().size()
              << " observed variables)" << std::endl;

  impl_->propagator.swap(propagator);
  return true;
}

const UFCongruencePropagator* UFBatchAdapter::congruencePropagator() const
{
  return impl_->propagator.get();
}

void UFBatchAdapter::clear()
{
  impl_->state.clearActive();
  impl_->equalityCache.clear();
  // beginQuery() calls this, and the backend that was consulting the
  // propagator is deleted at the end of every topLevelSTPOnce, before
  // either -- so nothing is left holding the pointer. Its atoms were that
  // solver's variables in any case.
  impl_->propagator.reset();
}
bool UFBatchAdapter::active() const
{
  return impl_->state.view != NULL && impl_->state.view->active();
}
UFCandidateOutcome UFBatchAdapter::checkCandidate(
    AbsRefine_CounterExample& counterexample)
{
  return checkOneCandidate(impl_->state, counterexample);
}
bool UFBatchAdapter::hasPendingLemma() const
{
  return !impl_->state.pending.empty();
}
void UFBatchAdapter::encodePendingLemmas(SATSolver& solver, ToSATBase* tosat)
{
  encodeLemmas(impl_->state, solver, tosat, -1, impl_->equalityCache);
  installCongruencePropagator(solver, tosat);
}
bool UFBatchAdapter::hasCertifiedModel() const
{
  return impl_->state.certified;
}
void UFBatchAdapter::invalidateCertifiedModel()
{
  impl_->state.certified = false;
  impl_->state.seed = UFFunctionModelSeedSet();
  impl_->state.handleValues.clear();
}
const UFFunctionModelSeedSet* UFBatchAdapter::certifiedModelSeed() const
{
  return impl_->state.certified ? &impl_->state.seed : NULL;
}
bool UFBatchAdapter::lookupCertifiedApplication(
    const ASTNode& durableHandle, UFConcreteValue& value) const
{
  return lookupCertified(impl_->state, durableHandle, value);
}
const LoweredApplicationView* UFBatchAdapter::applicationView() const
{
  return impl_->state.view;
}
const std::string& UFBatchAdapter::diagnostic() const
{
  return impl_->state.diagnostic;
}
uint64_t UFBatchAdapter::lemmasEmitted() const
{
  return impl_->state.emittedLemmaCount;
}

class UFPersistentAdapter::Impl
{
public:
  explicit Impl(STPMgr* manager) : state(manager) {}
  MutableAdapterState state;
  PersistentScopeKey activeScope;
  int positiveBlockLiteral = -1;
  uint64_t backendGeneration = 0;
  std::map<PersistentScopeKey, std::map<EqualityKey, CachedEquality>>
      equalityCaches;
};

UFPersistentAdapter::UFPersistentAdapter(STPMgr* manager)
    : impl_(new Impl(manager))
{
  assert(manager != NULL);
}
UFPersistentAdapter::~UFPersistentAdapter() = default;
void UFPersistentAdapter::beginBlock(const LoweredApplicationView* view,
                                     uint64_t epoch,
                                     uint64_t backendGeneration,
                                     uint64_t blockId,
                                     int positiveBlockLiteral)
{
  // Defend the adapter boundary as well as the driver's explicit reset hook:
  // a caller cannot accidentally reuse reification literals after replacing
  // its SAT solver merely by forgetting the notification.
  if (impl_->backendGeneration != backendGeneration)
    advanceBackendGeneration(backendGeneration);
  impl_->state.beginView(view);
  impl_->activeScope.epoch = epoch;
  impl_->activeScope.backendGeneration = backendGeneration;
  impl_->activeScope.block = blockId;
  impl_->positiveBlockLiteral = positiveBlockLiteral;
}
void UFPersistentAdapter::advanceBackendGeneration(
    uint64_t backendGeneration)
{
  if (impl_->backendGeneration == backendGeneration)
    return;
  clearActiveBlock();
  impl_->equalityCaches.clear();
  impl_->backendGeneration = backendGeneration;
  impl_->activeScope = PersistentScopeKey();
}
void UFPersistentAdapter::clearActiveBlock()
{
  impl_->state.clearActive();
  impl_->positiveBlockLiteral = -1;
}
void UFPersistentAdapter::clearEncodingEpoch()
{
  clearActiveBlock();
  impl_->equalityCaches.clear();
  impl_->activeScope = PersistentScopeKey();
}
void UFPersistentAdapter::invalidateCertifiedModel()
{
  impl_->state.certified = false;
  impl_->state.seed = UFFunctionModelSeedSet();
  impl_->state.handleValues.clear();
}
bool UFPersistentAdapter::active() const
{
  return impl_->state.view != NULL && impl_->state.view->active() &&
         impl_->positiveBlockLiteral >= 0;
}
UFCandidateOutcome UFPersistentAdapter::checkCandidate(
    AbsRefine_CounterExample& counterexample)
{
  return checkOneCandidate(impl_->state, counterexample);
}
bool UFPersistentAdapter::hasPendingLemma() const
{
  return !impl_->state.pending.empty();
}
void UFPersistentAdapter::encodePendingLemmas(SATSolver& solver,
                                              ToSATBase* tosat)
{
  if (!active())
    FatalError("persistent UF lemma has no active block scope");
  std::map<EqualityKey, CachedEquality>& cache =
      impl_->equalityCaches[impl_->activeScope];
  encodeLemmas(impl_->state, solver, tosat,
               impl_->positiveBlockLiteral ^ 1, cache);
}
bool UFPersistentAdapter::hasCertifiedModel() const
{
  return impl_->state.certified;
}
const UFFunctionModelSeedSet* UFPersistentAdapter::certifiedModelSeed() const
{
  return impl_->state.certified ? &impl_->state.seed : NULL;
}
bool UFPersistentAdapter::lookupCertifiedApplication(
    const ASTNode& durableHandle, UFConcreteValue& value) const
{
  return lookupCertified(impl_->state, durableHandle, value);
}
const LoweredApplicationView* UFPersistentAdapter::applicationView() const
{
  return impl_->state.view;
}
const std::string& UFPersistentAdapter::diagnostic() const
{
  return impl_->state.diagnostic;
}
uint64_t UFPersistentAdapter::lemmasEmitted() const
{
  return impl_->state.emittedLemmaCount;
}

} // namespace stp

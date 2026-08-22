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

#include "stp/UninterpretedFunctions/UFLowering.h"
#include "stp/Globals/Globals.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Util/DagWalk.h"
#include <algorithm>
#include <iostream>
#include <string>

namespace stp
{

namespace
{

unsigned bitsForDistinct(unsigned n)
{
  if (n <= 1)
    return 1;
  unsigned bits = 0;
  unsigned v = n;
  while (v > 0)
  {
    bits++;
    v >>= 1;
  }
  if (n == (1u << (bits - 1)))
    return bits - 1;
  return bits;
}

struct NarrowAnalysis
{
  std::map<const UFDecl*, unsigned> applicationCount;
  std::set<const UFDecl*> nonNarrowable;
};

NarrowAnalysis analyzeNarrowability(const ASTNode& root, UFContext* context)
{
  NarrowAnalysis result;
  ASTNodeSet visited;
  walkPreOrder(root, [&](const ASTNode& n) -> bool {
    if (!visited.insert(n).second)
      return false;

    if (n.GetKind() == UF_APPLY)
    {
      const UFDecl* decl = context->lookupIdentity(n[0]);
      if (decl)
        result.applicationCount[decl]++;
    }

    for (size_t i = 0; i < n.Degree(); i++)
    {
      if (n[i].GetKind() != UF_APPLY)
        continue;
      const UFDecl* childDecl = context->lookupIdentity(n[i][0]);
      if (!childDecl)
        continue;

      if (n.GetKind() != EQ)
      {
        result.nonNarrowable.insert(childDecl);
        continue;
      }
      size_t other = (i == 0) ? 1 : 0;
      if (other >= n.Degree() || n[other].GetKind() != UF_APPLY)
      {
        result.nonNarrowable.insert(childDecl);
        continue;
      }
      const UFDecl* otherDecl = context->lookupIdentity(n[other][0]);
      if (otherDecl != childDecl)
      {
        result.nonNarrowable.insert(childDecl);
        result.nonNarrowable.insert(otherDecl);
      }
    }
    return true;
  });
  return result;
}

bool isLeafActual(const ASTNode& actual)
{
  return actual.GetKind() == SYMBOL || actual.isConstant();
}

ASTNode rebuildWithChildren(const ASTNode& original,
                            const ASTVec& loweredChildren, STPMgr* manager)
{
  assert(original.Degree() == loweredChildren.size());
  bool changed = false;
  for (size_t i = 0; i < loweredChildren.size(); ++i)
    changed = changed || loweredChildren[i] != original[i];
  if (!changed)
    return original;

  NodeFactory* const factory = manager->defaultNodeFactory;
  ASTNode rebuilt;
  if (original.GetValueWidth() == 0)
    rebuilt = factory->CreateNode(original.GetKind(), loweredChildren);
  else
    // Mirror SubstitutionMap's rebuild funnel: CreateArrayTerm preserves both
    // widths for arrays and is also the width-preserving CreateTerm path for
    // non-Boolean bit-vector terms when the index width is zero.
    rebuilt =
        factory->CreateArrayTerm(original.GetKind(), original.GetIndexWidth(),
                                 original.GetValueWidth(), loweredChildren);

  if (rebuilt.GetSourceSort() != original.GetSourceSort())
    FatalError("UF lowering rebuilt a node at the wrong SourceSort", rebuilt);
  return rebuilt;
}

} // namespace

ASTNode
LoweredApplicationView::semanticRootWithDefinitions(STPMgr* manager) const
{
  assert(manager != NULL);
  if (namingDefinitions.empty() && sortConstraints.empty() &&
      congruenceConstraints.empty())
    return semanticRoot;
  ASTVec conjuncts;
  conjuncts.reserve(namingDefinitions.size() + sortConstraints.size() +
                    congruenceConstraints.size() + 1);
  conjuncts.push_back(semanticRoot);
  conjuncts.insert(conjuncts.end(), namingDefinitions.begin(),
                   namingDefinitions.end());
  conjuncts.insert(conjuncts.end(), sortConstraints.begin(),
                   sortConstraints.end());
  conjuncts.insert(conjuncts.end(), congruenceConstraints.begin(),
                   congruenceConstraints.end());
  return manager->defaultNodeFactory->CreateNode(AND, conjuncts);
}

UFLowering::UFLowering(STPMgr* manager) : manager_(manager)
{
  assert(manager_ != NULL);
}

namespace
{

bool allActualsConstant(const LoweredApplicationRecord& record)
{
  for (const ASTNode& actual : record.namedActuals)
    if (!actual.isConstant())
      return false;
  return true;
}

// C(n, 2) without overflowing on an absurd application count.
uint64_t pairsAmong(const uint64_t n)
{
  return n < 2 ? 0 : (n % 2 == 0 ? (n / 2) * (n - 1) : n * ((n - 1) / 2));
}

bool hasFloatingPointPosition(const UFSignature& signature)
{
  if (signature.codomain().kind() == SourceSort::Kind::FloatingPoint)
    return true;
  for (const SourceSort& sort : signature.domain())
    if (sort.kind() == SourceSort::Kind::FloatingPoint)
      return true;
  return false;
}

// One declaration's applications, partitioned so that only pairs drawn from
// the same part can ever be congruent, together with what those parts cost.
//
// The partition is z3's reduce_args grouping: a position at which *every*
// application holds a constant splits them by the value there, and two
// applications in different parts differ at a position where the pair loop
// sees two unequal constants and drops the pair. So the parts are both what
// to charge for and what to walk. Charging C(n, 2) over the whole declaration
// instead pushes it past a budget it fits inside -- measured, a declaration
// with a literal tag in one position was charged 4950 where it installs 450 --
// and walking the whole declaration instead spends time on pairs that can
// produce nothing.
//
// The estimate must be an upper bound on what the loop emits, never under it,
// or a declaration would spend budget it was not billed for. Within a part it
// is the established count: pairs among the applications with a symbolic
// actual somewhere, plus each all-constant application against each of those.
// Two all-constant applications are never charged, in a part or out of one,
// because they are either the same hash-consed handle or differ somewhere and
// are dropped.
//
// That last sentence is why a part carries its symbolic records first and says
// where they end. Being charged nothing is only half of it -- such a pair must
// not be *walked* either, and skipping it has to mean not iterating it, since a
// test still costs a loop step and these counts reach billions. Ordering the
// part is what lets the emit loop take the symbolic prefix as its outer range
// and get C(symbolic, 2) + constant * symbolic exactly, the estimate term for
// term.
struct CongruencePart
{
  std::vector<const LoweredApplicationRecord*> records;
  size_t symbolic = 0;
};

struct CongruenceGroups
{
  std::vector<CongruencePart> parts;
  uint64_t estimate = 0;
};

CongruenceGroups
groupForCongruence(const std::vector<const LoweredApplicationRecord*>& records)
{
  CongruenceGroups grouped;
  if (records.size() < 2)
    return grouped;
  const size_t arity = records.front()->loweredActuals.size();

  // Positions at which *every* application holds a constant. The quantifier
  // has to be "every", not "here": "these two cannot be shown distinct" is
  // not a transitive relation -- for arity two, (1,x), (1,2) and (3,2) relate
  // the first to the second and the second to the third but not the first to
  // the third -- so no partition models it. Restricting to positions that are
  // constant throughout is what makes it an equivalence, and is the same
  // restriction z3's reduce_args makes for the same reason.
  std::vector<bool> constantEverywhere(arity, true);
  for (const LoweredApplicationRecord* record : records)
    for (size_t i = 0; i < arity; ++i)
      if (!record->loweredActuals[i].isConstant())
        constantEverywhere[i] = false;

  std::map<ASTVec, size_t> partIndex;
  for (const LoweredApplicationRecord* record : records)
  {
    ASTVec key;
    for (size_t i = 0; i < arity; ++i)
      if (constantEverywhere[i])
        key.push_back(record->loweredActuals[i]);
    const auto found = partIndex.find(key);
    if (found == partIndex.end())
    {
      partIndex.emplace(key, grouped.parts.size());
      grouped.parts.push_back(CongruencePart());
      grouped.parts.back().records.push_back(record);
    }
    else
      grouped.parts[found->second].records.push_back(record);
  }

  for (CongruencePart& part : grouped.parts)
  {
    // Symbolic first, all-constant after, and the charge read off the same
    // split the walk will use. Written as one stable partition rather than
    // two counts so the two cannot drift: whatever ends up before `symbolic`
    // is exactly what the emit loop takes as its outer range.
    const auto boundary = std::stable_partition(
        part.records.begin(), part.records.end(),
        [](const LoweredApplicationRecord* record) {
          return !allActualsConstant(*record);
        });
    part.symbolic = (size_t)(boundary - part.records.begin());
    const uint64_t constantArgued = part.records.size() - part.symbolic;
    grouped.estimate +=
        pairsAmong(part.symbolic) + constantArgued * part.symbolic;
  }
  return grouped;
}

// What one argument position of a candidate pair contributes to the premise.
enum class PositionVerdict
{
  Distinct,  // the two actuals can never be equal: the pair needs no constraint
  Identical, // they always are: the premise atom is true and drops
  Unknown    // the premise atom has to be built
};

// Ask the *lowered* actuals, not the named ones. A compound actual is named by
// a fresh symbol, so asking the names can only ever catch two literal
// constants -- which is why a function applied at a sliding offset, f(i),
// f(i+1), ..., got a full C(n,2) set of constraints whose premises are all
// unsatisfiable. The lowered terms hand the question to the node factory,
// which already cancels a common addend out of two BVPLUSes and folds
// (= (bvadd i 1) (bvadd i 2)) to false on its own.
//
// Whatever the factory cannot decide stays Unknown, so a factory without those
// rewrites (the C API's default hashing factory) simply prunes nothing. The
// premise is still stated over the named actuals: only the *test* moves.
PositionVerdict comparePosition(NodeFactory* factory, const ASTNode& left,
                                const ASTNode& right, const SourceSort& sort)
{
  // Interning makes equal constants one node, so the first two tests are
  // exact and hold whatever factory is installed -- the C API leaves the
  // plain hashing factory in place, and it folds nothing.
  if (left == right)
    return PositionVerdict::Identical;
  if (left.isConstant() && right.isConstant())
    return PositionVerdict::Distinct;
  const ASTNode folded = factory->CreateNode(
      sort.kind() == SourceSort::Kind::Bool ? IFF : EQ, left, right);
  if (folded.GetKind() == TRUE)
    return PositionVerdict::Identical;
  if (folded.GetKind() == FALSE)
    return PositionVerdict::Distinct;
  return PositionVerdict::Unknown;
}

} // namespace

// Eager congruence (UFSTP OPT-02/OPT-03). The constraints are built as AST and
// conjoined to the semantic root rather than encoded straight to CNF, which
// buys three things: both solve modes pick them up through the one function
// that already attaches naming definitions, a persistent block inherits its
// guard with no new guard logic, and ordinary preprocessing gets to simplify
// or delete constraints whose results nothing constrains.
void UFLowering::installEagerCongruence(
    LoweredApplicationView& view, const std::set<const UFDecl*>& injectable,
    const ASTNode& guard) const
{
  typedef UserDefinedFlags::UFEagerMode Mode;
  const Mode mode = manager_->UserFlags.uf_eager_mode;
  view.eagerStats.budget = manager_->UserFlags.uf_eager_budget;
  if (mode == Mode::OFF || view.applications.empty())
    return;
  view.eagerStats.policyRan = true;

  std::map<const UFDecl*, std::vector<const LoweredApplicationRecord*>>
      byDeclaration;
  for (const LoweredApplicationRecord& record : view.applications)
  {
    // A record with no readable argument tuple belongs to a declaration with
    // one application, which has no pairs to constrain anyway.
    if (record.observableArguments)
      byDeclaration[record.declaration].push_back(&record);
  }

  // Cost of each candidate declaration, cheapest first: two applications
  // whose actuals are all constants are either the same durable handle or
  // differ in some position, so they never need a constraint between them.
  std::vector<std::pair<uint64_t, const UFDecl*>> selection;
  std::map<const UFDecl*, size_t> statIndex;
  std::map<const UFDecl*, CongruenceGroups> groupsByDeclaration;
  for (const auto& entry : byDeclaration)
  {
    const CongruenceGroups grouped = groupForCongruence(entry.second);
    const uint64_t cost = grouped.estimate;
    groupsByDeclaration.emplace(entry.first, grouped);

    UFEagerDeclarationStat stat;
    stat.name = entry.first->name();
    stat.applications = entry.second.size();
    stat.estimatedPairs = cost;
    stat.outcome = UFEagerDeclarationStat::Outcome::NoComparablePairs;
    statIndex[entry.first] = view.eagerStats.declarations.size();
    view.eagerStats.declarations.push_back(stat);

    if (cost != 0)
      selection.push_back(std::make_pair(cost, entry.first));
  }
  // Cheapest first, but every floating-point signature after every
  // bit-vector one whatever they cost.
  //
  // A float pair is worth less than a bit-vector pair of the same count: the
  // query's own (= a b) over bit-vectors is a substitutable equality, so
  // equality propagation collapses the actuals and the constraints dissolve
  // before SAT, while over floats it is FP_SMT_EQ, a predicate, and every
  // constraint is paid in full. Sorting floats last is what that difference
  // buys them -- they take whatever budget is left rather than competing for
  // it, so the declarations a pure bit-vector query selects are exactly the
  // ones it selected when floats were refused outright, and a cheap float
  // declaration can no longer push an expensive bit-vector one over the line.
  std::sort(selection.begin(), selection.end(),
            [](const std::pair<uint64_t, const UFDecl*>& left,
               const std::pair<uint64_t, const UFDecl*>& right) {
              const bool leftFloat =
                  hasFloatingPointPosition(left.second->signature());
              const bool rightFloat =
                  hasFloatingPointPosition(right.second->signature());
              if (leftFloat != rightFloat)
                return rightFloat;
              if (left.first != right.first)
                return left.first < right.first;
              return left.second->id() < right.second->id();
            });

  NodeFactory* const factory = manager_->defaultNodeFactory;
  uint64_t budget = manager_->UserFlags.uf_eager_budget;
  for (const std::pair<uint64_t, const UFDecl*>& candidate : selection)
  {
    UFEagerDeclarationStat& stat =
        view.eagerStats.declarations[statIndex[candidate.second]];
    if (mode == Mode::AUTO)
    {
      // A float pair is worth less than a bit-vector pair of the same
      // count, which is why the ordering above puts every float signature
      // after every bit-vector one: they take what is left rather than
      // competing for it. Where the actuals are bit-vectors the query's own
      // (= a b) is a substitutable equality, so equality propagation
      // collapses them and the constraints dissolve before SAT; where they
      // are floats it is FP_SMT_EQ, a predicate, and every constraint is paid
      // in full.
      //
      // They used to be refused outright, which was right while the budget
      // was 4096: that admitted a float declaration of up to 91 applications,
      // and the shape the refusal was reasoned from -- actuals asserted
      // equal, results distinct -- costs eager 1.6s and climbing at that
      // size. At 256 the budget admits at most 23 float applications, and
      // measured across that whole band the refusal costs more than it saves:
      // the shape it protected loses 0.04s at the top of the band, while free
      // float arguments with distinct results gain 0.52s, and a float
      // codomain over a bit-vector domain, a NaN-heavy query and compound
      // float actuals are each within 0.1s or favour selecting. The budget,
      // not a veto, is what keeps the bad shape cheap now, and it truncates
      // that shape before its superlinear part begins.
      if (candidate.first > budget)
      {
        // Pass over this one and keep going. Stopping here would be right if
        // the order were cheapest-first throughout, but it is cheapest-first
        // within the bit-vector signatures and then again within the float
        // ones, so a bit-vector declaration that does not fit says nothing
        // about the floats queued behind every bit-vector one. Stopping was
        // what made "floats take what is left" untrue: a float declaration of
        // ten pairs was passed over because a bit-vector declaration of three
        // hundred came first, while the same ten-pair declaration was selected
        // when its signature was bit-vectors. It also left the float one
        // labelled as having had no comparable pairs on a line that reported
        // ten.
        stat.outcome = UFEagerDeclarationStat::Outcome::DeclinedBudget;
        continue;
      }
      budget -= candidate.first;
      view.eagerStats.budgetSpent += candidate.first;
    }
    stat.outcome = UFEagerDeclarationStat::Outcome::Selected;

    // Walk exactly what was charged for, and nothing else. Two kinds of pair
    // are charged nothing because they can produce nothing, and each has to be
    // skipped by not being iterated rather than by being tested and dropped --
    // a test still costs a loop step, and the counts here reach billions.
    //
    // Across parts: the pair differs at a position where both hold constants.
    // Within a part, between two all-constant applications: they are either
    // the same durable handle or they differ somewhere, and where they differ
    // both hold constants again. The outer range is therefore the part's
    // symbolic prefix, which makes the walk C(symbolic, 2) + constant *
    // symbolic -- the estimate, term for term.
    //
    // Counting them instead is not a small waste. One part of 60 000
    // all-constant applications is charged one pair and was enumerated
    // 1 799 970 001 times, 20.5 s against 1.5 s with the policy off, and it
    // grew quadratically from there.
    const UFSignature& signature = candidate.second->signature();
    for (const CongruencePart& part : groupsByDeclaration[candidate.second].parts)
    {
    const std::vector<const LoweredApplicationRecord*>& records = part.records;
    for (size_t i = 0; i < part.symbolic; ++i)
      for (size_t j = i + 1; j < records.size(); ++j)
      {
        const LoweredApplicationRecord& left = *records[i];
        const LoweredApplicationRecord& right = *records[j];
        stat.enumeratedPairs++;
        ASTVec premise;
        bool impossible = false;
        for (size_t k = 0; k < signature.arity() && !impossible; ++k)
        {
          const SourceSort solved =
              UFSignature::loweringSort(signature.domain()[k]);
          switch (comparePosition(factory, left.loweredActuals[k],
                                  right.loweredActuals[k], solved))
          {
            case PositionVerdict::Identical:
              continue; // the premise atom is true and drops
            case PositionVerdict::Distinct:
              // These two can never be congruent, so the pair needs no
              // constraint at all.
              impossible = true;
              continue;
            case PositionVerdict::Unknown:
              break;
          }
          premise.push_back(factory->CreateNode(
              solved.kind() == SourceSort::Kind::Bool ? IFF : EQ,
              left.namedActuals[k], right.namedActuals[k]));
        }
        if (impossible)
        {
          stat.skippedImpossiblePairs++;
          continue;
        }
        stat.emittedConstraints++;

        const ASTNode conclusion = factory->CreateNode(
            signature.codomain().kind() == SourceSort::Kind::Bool ? IFF : EQ,
            left.resultSymbol, right.resultSymbol);
        const ASTNode premiseConj =
            premise.empty()
                ? ASTNode()
                : premise.size() == 1
                      ? premise[0]
                      : factory->CreateNode(AND, premise);
        view.congruenceConstraints.push_back(
            premise.empty()
                ? conclusion
                : factory->CreateNode(IMPLIES, premiseConj, conclusion));

        if (!premise.empty() &&
            injectable.count(candidate.second) != 0)
        {
          // The converse of congruence, and the one constraint here that is
          // not entailed by the query: it says this declaration is injective
          // on the pair, which the caller never asserted. It goes in behind
          // the activation symbol so that a refutation resting on it can be
          // taken back rather than reported -- see
          // STPMgr::solveRetractingInjectivity. Counted separately, because
          // the guard is only sound if every one of them is behind it, and a
          // driver with no way to assume the guard has to know that these
          // exist at all.
          stat.emittedInjectivity++;
          const ASTNode converse =
              factory->CreateNode(IMPLIES, conclusion, premiseConj);
          view.congruenceConstraints.push_back(
              guard.IsNull() ? converse
                             : factory->CreateNode(IMPLIES, guard, converse));
        }
      }
    }
  }
}

// Observability for the eager policy. Without this the only way to tell a
// declined declaration from one that had nothing to install is to edit a flag
// and compare wall clock, which is how every calibration of this policy has
// had to be done. One line per declaration that had pairs to consider, plus a
// total; nothing is printed when the policy did not run.
void UFLowering::reportEagerCongruence(const LoweredApplicationView& view) const
{
  if (!manager_->UserFlags.stats_flag)
    return;
  const UFEagerStats& stats = view.eagerStats;
  if (!stats.policyRan)
  {
    if (!view.applications.empty())
      std::cerr << "UF: eager congruence policy off, "
                << view.applications.size() << " application(s) left to the "
                << "refinement loop" << std::endl;
    return;
  }
  // By name, not in the order the declarations were collected: that order is
  // the address order of the declaration records, so it varies between two
  // runs of the same query and between two queries of the same shape. A
  // fixture that reads one line after another was pinning the allocator.
  std::vector<const UFEagerDeclarationStat*> ordered;
  ordered.reserve(stats.declarations.size());
  for (const UFEagerDeclarationStat& stat : stats.declarations)
    ordered.push_back(&stat);
  std::stable_sort(ordered.begin(), ordered.end(),
                   [](const UFEagerDeclarationStat* left,
                      const UFEagerDeclarationStat* right) {
                     return left->name < right->name;
                   });
  for (const UFEagerDeclarationStat* entry : ordered)
  {
    const UFEagerDeclarationStat& stat = *entry;
    if (stat.estimatedPairs == 0)
      continue;
    std::cerr << "UF: eager " << stat.outcomeName() << " " << stat.name << " ("
              << stat.applications << " applications, " << stat.estimatedPairs
              << " pairs estimated";
    if (stat.outcome == UFEagerDeclarationStat::Outcome::Selected)
      std::cerr << ", " << stat.enumeratedPairs << " enumerated, "
                << stat.skippedImpossiblePairs << " impossible, "
                << stat.emittedConstraints << " constraints";
    std::cerr << ")" << std::endl;
  }
  std::cerr << "UF: eager total " << stats.selectedDeclarations() << "/"
            << stats.declarations.size() << " declarations, "
            << stats.emittedConstraints() << " constraints, budget "
            << stats.budgetSpent << "/" << stats.budget << " spent"
            << std::endl;
  if (stats.emittedInjectivity() != 0)
    std::cerr << "UF: eager " << stats.emittedInjectivity()
              << " of those assume injectivity (--uf-inject-args), behind one "
              << "guard the search can be asked about and withdraw"
              << std::endl;
}

LoweredApplicationView
UFLowering::lowerCompletedRoot(const ASTNode& publicRoot,
                               const UFSolveScope& scope) const
{
  if (publicRoot.IsNull() || !publicRoot.IsOwnedBy(manager_))
    FatalError("UF lowering requires a completed root owned by its context");

  LoweredApplicationView view;
  view.scope = scope;
  view.publicRoot = publicRoot;
  view.semanticRoot = publicRoot;

  UFContext* context = manager_->getUFContextIfAny();
  if (!manager_->UserFlags.enable_uninterpreted_functions)
  {
    if (context != NULL)
      context->releaseSolveProtection();
    return view;
  }

  if (context == NULL)
  {
    if (containsKind(publicRoot, UF_APPLY))
      FatalError("UF lowering found UF_APPLY without a manager context",
                 publicRoot);
    return view;
  }
  context->beginSolveProtection();

  // Pre-analysis: detect UF declarations whose results are used only for
  // equality with other results of the same declaration. Their result sort
  // can be narrowed from the declared width to ceil(log2(N+1)) bits,
  // cutting the AIG cost of every congruence constraint from O(width) to
  // O(log N).
  NarrowAnalysis narrowing;
  if (manager_->UserFlags.uf_narrow_results ||
      manager_->UserFlags.uf_inject_args)
    narrowing = analyzeNarrowability(publicRoot, context);

  // A name is canonical per lowered expression, matching the reference
  // oracle. This both avoids redundant definitions and makes an identical
  // persistent block reconstruct the identical semantic root.
  ASTNodeMap scalarNames;

  // Pin every RoundingMode scalar this lowering makes the checker's authority
  // for -- introduced results, introduced argument names, and the leaf
  // symbols it registers as solve scalars in their own right. The sort has
  // five values and its carrier thirty-two, so an unpinned one lets a model
  // name no mode at all: the generated define-fun would print a term of no
  // sort, and model evaluation could hand an illegal mode to an enclosing
  // floating-point operation as a constant operand.
  //
  // FpTotalise pins the same symbols out of the semantic root when it runs,
  // and an OR of five equalities is idempotent, so at worst this adds a
  // duplicate conjunct. What it buys is that the pin arrives with the symbol
  // instead of with a later pass: the persistent path decides whether to run
  // that pass from the *raw* block, and reset-assertions can retract a
  // declaration's own pin while keeping the declaration.
  //
  // Pins are appended in walk order rather than collected from
  // view.solveScalars, so that an identical block rebuilds an identical
  // conjunction without depending on a hash set's iteration order.
  ASTNodeSet pinnedRoundingModes;
  const auto pinIfRoundingMode = [&](const ASTNode& scalar) {
    if (!manager_->isRoundingModeSymbol(scalar) ||
        !pinnedRoundingModes.insert(scalar).second)
      return;
    view.sortConstraints.push_back(
        manager_->roundingModeValidConstraint(scalar));
  };

  // An actual, as the checker will compare it. Only a float moves: it becomes
  // its canonical packed bits, which is the sort's own equality rather than
  // the carrier's, so two NaNs of different payloads compare equal and the
  // two zeros stay apart. A constant takes the same boundary as everything
  // else -- it needs no special case, because a float constant is already
  // interned canonically (STPMgr::CreateFPConst quotients NaN) and the
  // boundary folds over it rather than building a circuit.
  const auto canonicalActual = [&](const ASTNode& lowered,
                                   const SourceSort& declared) -> ASTNode {
    if (declared.kind() != SourceSort::Kind::FloatingPoint)
      return lowered;
    return manager_->defaultNodeFactory->CreateTerm(
        FP_TO_IEEE_BV, declared.packedWidth(), lowered);
  };

  // A result, as the formula that replaces the application will see it. The
  // exact inverse of canonicalActual: the three-child to_fp reinterprets the
  // solved bits at the declared format.
  const auto theoryResult = [&](const ASTNode& result,
                                const SourceSort& declared) -> ASTNode {
    if (declared.kind() != SourceSort::Kind::FloatingPoint)
      return result;
    const ASTNode reinterpreted = manager_->defaultNodeFactory->CreateTerm(
        FP_TOFP, declared.packedWidth(),
        manager_->CreateBVConst(32, declared.exponentWidth()),
        manager_->CreateBVConst(32, declared.significandWidth()), result);
    if (reinterpreted.GetSourceSort() != declared)
      FatalError("UF lowering rebuilt a float result at the wrong SourceSort",
                 reinterpreted);
    return reinterpreted;
  };

  std::set<const UFDecl*> reportedNarrow;

  // A compound actual cannot be named while the walk is running: whether the
  // name is needed depends on how many applications its declaration turns out
  // to have, and the last of them may not have been reached yet. Each one is
  // parked here against the slot it will fill.
  struct PendingName
  {
    size_t record;
    size_t argument;
    ASTNode lowered;
    SourceSort sort;
  };
  std::vector<PendingName> pendingNames;

  // Rewrite the completed root once, bottom-up. The explicit walk keeps its
  // frames on the heap (input controls AST depth), visits each shared DAG node
  // once, and guarantees that a nested UF application has become its scalar
  // result before an enclosing application's actual is recorded.
  DenseNodeMap rewritten;
  view.semanticRoot = postOrderRebuild(
      publicRoot, rewritten,
      [&](const ASTNode& application, const ASTVec& loweredChildren) -> ASTNode
      {
        if (application.GetKind() != UF_APPLY)
          return rebuildWithChildren(application, loweredChildren, manager_);

        std::string diagnostic;
        if (!context->isRegisteredApplication(application) ||
            !context->validateApplicationChildren(application.GetChildren(),
                                                  &diagnostic))
          FatalError(("UF lowering rejected a malformed durable application: " +
                      diagnostic)
                         .c_str(),
                     application);
        if (!context->isActiveApplication(application))
          FatalError("UF lowering rejected a stale or inactive durable "
                     "application",
                     application);

        const UFDecl* declaration = context->lookupIdentity(application[0]);
        if (declaration == NULL)
          FatalError("UF lowering could not recover declaration identity",
                     application);
        if (loweredChildren.size() != application.Degree() ||
            loweredChildren.empty() || loweredChildren[0] != application[0])
          FatalError("UF lowering rewrote a declaration identity", application);

        LoweredApplicationRecord record;
        record.durableHandle = application;
        record.declaration = declaration;
        record.scope = scope;
        record.stableOrder = view.applications.size();
        record.loweredActuals.reserve(application.Degree() - 1);
        record.namedActuals.reserve(application.Degree() - 1);

        for (size_t i = 1; i < loweredChildren.size(); ++i)
        {
          const ASTNode& lowered = loweredChildren[i];
          const SourceSort& expected = declaration->signature().domain()[i - 1];
          if (application[i].GetSourceSort() != expected ||
              lowered.GetSourceSort() != expected)
            FatalError("UF lowering crossed a SourceSort boundary",
                       application);

          // From here down the record speaks the lowering sort. For every
          // sort but FloatingPoint that is the declared sort unchanged; a
          // float crosses into its canonical packed carrier here and does not
          // cross back until the model boundary.
          const SourceSort solved = UFSignature::loweringSort(expected);
          const ASTNode scalar = canonicalActual(lowered, expected);
          if (scalar.GetSourceSort() != solved)
            FatalError("UF lowering produced an actual at the wrong lowering "
                       "sort",
                       scalar);
          record.loweredActuals.push_back(scalar);

          if (isLeafActual(scalar))
          {
            record.namedActuals.push_back(scalar);
            // A source symbol is already its own canonical scalar name, but it
            // still participates in future direct-CNF lemmas. Protect/register it
            // exactly like an introduced name so ordinary preprocessing cannot
            // substitute it away and leave the lemma talking about an unlinked
            // fresh SAT value. Constants need no mapping or protection.
            if (scalar.GetKind() == SYMBOL)
            {
              view.protectedSymbols.insert(scalar);
              view.solveScalars.insert(scalar);
              pinIfRoundingMode(scalar);
            }
            continue;
          }

          PendingName pending;
          pending.record = record.stableOrder;
          pending.argument = record.namedActuals.size();
          pending.lowered = scalar;
          pending.sort = solved;
          pendingNames.push_back(pending);
          record.namedActuals.push_back(ASTNode());
        }

        const SourceSort& codomain = declaration->signature().codomain();
        if (application.GetSourceSort() != codomain)
          FatalError("UF lowering found a durable result with the wrong "
                     "SourceSort",
                     application);
        SourceSort solvedCodomain = UFSignature::loweringSort(codomain);
        // The name a narrowed result gets has to say how wide it is. The
        // deterministic namespace keys a symbol on the application alone, and
        // its contract is that the key settles the sort -- one key, one
        // symbol, one sort, so that an identical block rebuilds an identical
        // root. A narrowed width does not keep that bargain: it is read off
        // how many applications the *current* root has, and the same durable
        // application is lowered again in the next solve with a different
        // count behind it. Two applications of f under a push, three after
        // the pop, and the same handle wants one bit and then two.
        //
        // So the width joins the key rather than silently disagreeing with
        // it. Only a result that was actually narrowed is tagged, which
        // leaves every unnarrowed name exactly as it was -- including the
        // rounding-mode results a persistent block has to rebuild and re-pin
        // by name.
        std::string resultPrefix = "uf_result";
        if (manager_->UserFlags.uf_narrow_results &&
            solvedCodomain.kind() == SourceSort::Kind::BitVector &&
            narrowing.nonNarrowable.count(declaration) == 0)
        {
          auto it = narrowing.applicationCount.find(declaration);
          if (it != narrowing.applicationCount.end())
          {
            const unsigned narrowWidth =
                bitsForDistinct(it->second);
            if (narrowWidth < solvedCodomain.bitVectorWidth())
            {
              solvedCodomain = SourceSort::bitVector(narrowWidth);
              resultPrefix += "_w" + std::to_string(narrowWidth);
              if (manager_->UserFlags.stats_flag &&
                  reportedNarrow.insert(declaration).second)
                std::cerr << "UF: narrowing result of "
                          << declaration->name() << " from "
                          << codomain.bitVectorWidth() << " to "
                          << narrowWidth << " bits (" << it->second
                          << " applications)" << std::endl;
            }
          }
        }
        record.resultSymbol = manager_->CreateDeterministicSourceVariable(
            solvedCodomain, resultPrefix, application);
        if (record.resultSymbol.GetSourceSort() != solvedCodomain)
          FatalError("UF lowering allocated a result at the wrong SourceSort",
                     record.resultSymbol);
        view.protectedSymbols.insert(record.resultSymbol);
        view.solveScalars.insert(record.resultSymbol);
        pinIfRoundingMode(record.resultSymbol);
        view.handleToResult.insert(
            std::make_pair(application, record.resultSymbol));
        view.applications.push_back(record);
        // A float result is solved as a packed bit-vector but the formula it
        // replaces expects a float, so it goes back in through the exact
        // inverse of the boundary its arguments came through: the three-child
        // "reinterpret these bits" to_fp. Every other sort is returned as
        // itself.
        return theoryResult(record.resultSymbol, codomain);
      });

  // Only a declaration with two or more lowered applications can ever produce
  // a congruence lemma, and a name for a compound actual exists solely so that
  // such a lemma has a scalar to equate. Naming one for a lone application
  // costs a protected symbol and a defining equality that drag the whole
  // argument expression into the bit-blast, where nothing can observe it.
  //
  // Two rounds, so that the decision does not depend on the order the walk
  // reached things: every name a comparable record needs is created first, and
  // a lone application sharing one of those terms then reuses it and stays
  // readable for free. Only an actual left without a name after both rounds
  // makes its record unobservable.
  std::map<const UFDecl*, size_t> applicationsPerDeclaration;
  for (const LoweredApplicationRecord& record : view.applications)
    applicationsPerDeclaration[record.declaration]++;

  const auto comparable = [&](const PendingName& pending) {
    return applicationsPerDeclaration[view.applications[pending.record]
                                          .declaration] > 1;
  };

  for (const PendingName& pending : pendingNames)
  {
    if (!comparable(pending))
      continue;
    ASTNode name;
    const ASTNodeMap::const_iterator found = scalarNames.find(pending.lowered);
    if (found != scalarNames.end())
      name = found->second;
    else
    {
      name = manager_->CreateDeterministicSourceVariable(pending.sort, "uf_arg",
                                                         pending.lowered);
      if (name.GetSourceSort() != pending.sort)
        FatalError("UF lowering allocated an argument name at the wrong "
                   "SourceSort",
                   name);
      scalarNames.insert(std::make_pair(pending.lowered, name));
      view.nameToTerm.insert(std::make_pair(name, pending.lowered));
      view.protectedSymbols.insert(name);
      view.solveScalars.insert(name);
      pinIfRoundingMode(name);
      view.namingDefinitions.push_back(
          manager_->defaultNodeFactory->CreateNode(
              pending.sort.kind() == SourceSort::Kind::Bool ? IFF : EQ, name,
              pending.lowered));
    }
    view.applications[pending.record].namedActuals[pending.argument] = name;
  }

  for (const PendingName& pending : pendingNames)
  {
    if (comparable(pending))
      continue;
    LoweredApplicationRecord& record = view.applications[pending.record];
    const ASTNodeMap::const_iterator found = scalarNames.find(pending.lowered);
    if (found != scalarNames.end())
      record.namedActuals[pending.argument] = found->second;
    else
      record.observableArguments = false;
  }

  // An unobservable record keeps its durable handle, its result symbol and its
  // lowered actuals; what it does not keep is a half-filled scalar tuple that
  // no checker round may read.
  for (LoweredApplicationRecord& record : view.applications)
    if (!record.observableArguments)
      record.namedActuals.clear();

  std::set<const UFDecl*> injectable;
  ASTNode injectivityGuard;
  if (manager_->UserFlags.uf_inject_args)
  {
    for (const auto& entry : narrowing.applicationCount)
      if (narrowing.nonNarrowable.count(entry.first) == 0)
        injectable.insert(entry.first);

    // Minted before the pair loop rather than on first use, so that every
    // converse implication of this lowering is behind the same symbol and
    // withdrawing it withdraws all of them. Keyed on the root being lowered,
    // which is what makes an identical persistent block rebuild an identical
    // guard along with an identical semantic root.
    if (!injectable.empty())
      injectivityGuard = manager_->CreateDeterministicSourceVariable(
          SourceSort::boolean(), "uf_inject_guard", publicRoot);
  }

  installEagerCongruence(view, injectable, injectivityGuard);
  reportEagerCongruence(view);

  // Tell the driver what this lowering assumed, and how to take it back. It is
  // the driver that holds the verdict, and this is the one thing installed
  // here that the verdict depends on: everything else in the encoding is
  // entailed by the query, so only these implications can turn a satisfiable
  // query unsatisfiable.
  //
  // The guard is registered as protected only when it is actually load-bearing.
  // A lowering that installed no converse implication has nothing to retract
  // and must not leave a free symbol behind for the simplifier to carry.
  if (view.eagerStats.emittedInjectivity() != 0)
  {
    view.injectivityGuard = injectivityGuard;
    // Without this the simplifier is free to do exactly what the guard was
    // built to allow -- observe that nothing constrains it, set it false, and
    // delete every implication behind it. That is sound, but it silently
    // turns the flag off. RemoveUnconstrained and SubstitutionMap both honour
    // this set.
    view.protectedSymbols.insert(injectivityGuard);
  }
  manager_->noteInjectivityAssumed(view.eagerStats.emittedInjectivity(),
                                   view.eagerStats.injectiveDeclarations(),
                                   view.injectivityGuard);

  // This checks the whole barrier once, including the naming definitions.
  // Scanning every progressively larger actual separately would turn a
  // linear post-order rewrite back into a quadratic algorithm on shared
  // nested DAGs.
  if (containsKind(view.semanticRootWithDefinitions(manager_), UF_APPLY))
    FatalError("UF_APPLY crossed the completed-root lowering barrier",
               view.semanticRoot);

  context->installSolveProtection(view.protectedSymbols, view.solveScalars);
  return view;
}

} // namespace stp

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

// Native UF refinement clauses must be fully reified and, in the persistent
// adapter, every helper and semantic clause must carry the exact-stack block
// guard.  These tests drive the production checker and adapters with a
// concrete candidate, then inspect a backend-neutral recording SAT solver.

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFLowering.h"
#include "stp/UninterpretedFunctions/UFRefinement.h"

#include <gtest/gtest.h>
#include <algorithm>
#include <vector>

using namespace stp;

namespace
{

class RecordingSolver final : public SATSolver
{
public:
  explicit RecordingSolver(unsigned firstFresh) : next_(firstFresh) {}

  bool okay() const override { return true; }
  uint8_t modelValue(uint32_t) const override { return undef_literal(); }
  uint32_t newVar() override
  {
    if (rejectMutation_)
      FatalError("test observed SAT mutation before UF leaf validation");
    return next_++;
  }
  uint32_t nVars() const override { return next_; }
  void printStats() const override {}
  void setVerbosity(int) override {}
  lbool true_literal() const override { return 0; }
  lbool false_literal() const override { return 1; }
  lbool undef_literal() const override { return 2; }

  unsigned nextVariable() const { return next_; }
  const std::vector<std::vector<int>>& clauses() const { return clauses_; }
  void rejectMutation() { rejectMutation_ = true; }

protected:
  bool addClauseInternal(const vec_literals& clause) override
  {
    if (rejectMutation_)
      FatalError("test observed SAT mutation before UF leaf validation");
    std::vector<int> copy;
    for (int i = 0; i < clause.size(); ++i)
      copy.push_back(toInt(clause[i]));
    clauses_.push_back(copy);
    return true;
  }
  bool solveInternal(bool&) override { return false; }

private:
  unsigned next_;
  bool rejectMutation_ = false;
  std::vector<std::vector<int>> clauses_;
};

class RecordingToSAT final : public ToSATBase
{
public:
  explicit RecordingToSAT(STPMgr* manager) : ToSATBase(manager) {}

  bool CallSAT(SATSolver&, const ASTNode&, bool) override { return false; }
  ASTNodeToSATVar& SATVar_to_SymbolIndexMap() override { return bindings_; }
  void ClearAllTables() override { bindings_.clear(); }

  void bind(const ASTNode& node, std::initializer_list<unsigned> variables)
  {
    bindings_[node] = std::vector<unsigned>(variables);
  }

  void unbind(const ASTNode& node) { bindings_.erase(node); }

private:
  ASTNodeToSATVar bindings_;
};

struct RefinementFixture
{
  STPMgr manager;
  SubstitutionMap substitutions;
  Simplifier simplifier;
  ArrayTransformer transformer;
  AbsRefine_CounterExample counterexample;
  UFContext* context;
  const UFDecl* function;
  ASTNode a;
  ASTNode b;
  ASTNode left;
  ASTNode right;
  LoweredApplicationView batchView;
  LoweredApplicationView persistentView;
  RecordingToSAT tosat;

  RefinementFixture()
      : substitutions(&manager), simplifier(&manager, &substitutions),
        transformer(&manager, &simplifier),
        counterexample(&manager, &simplifier, &transformer), context(NULL),
        function(NULL), tosat(&manager)
  {
    manager.UserFlags.enable_uninterpreted_functions = true;
    context = manager.getUFContext();
    std::string diagnostic;
    function = context->declareFunction(
        "f", {SourceSort::boolean()}, SourceSort::bitVector(2),
        &diagnostic);
    EXPECT_NE(nullptr, function) << diagnostic;
    a = manager.CreateSourceSymbol("a", SourceSort::boolean());
    b = manager.CreateSourceSymbol("b", SourceSort::boolean());
    left = context->apply(function, {a}, &diagnostic);
    right = context->apply(function, {b}, &diagnostic);
    const ASTNode root = manager.defaultNodeFactory->CreateNode(
        NOT, manager.defaultNodeFactory->CreateNode(EQ, left, right));
    UFLowering lowerer(&manager);
    batchView = lowerer.lowerCompletedRoot(root, UFSolveScope::batch(1));
    persistentView = lowerer.lowerCompletedRoot(
        root, UFSolveScope::persistent(9, 7));

    populate(batchView);
    populate(persistentView);
  }

  void populate(const LoweredApplicationView& view)
  {
    ASSERT_EQ(2u, view.applications.size());
    for (const LoweredApplicationRecord& record : view.applications)
    {
      const bool isLeft = record.durableHandle == left;
      counterexample.InsertIntoCounterExampleMap(
          record.namedActuals[0], manager.CreateNode(TRUE));
      counterexample.InsertIntoCounterExampleMap(
          record.resultSymbol, manager.CreateBVConst(2, isLeft ? 1 : 2));
      if (isLeft)
      {
        tosat.bind(record.namedActuals[0], {0});
        tosat.bind(record.resultSymbol, {2, 3});
      }
      else
      {
        tosat.bind(record.namedActuals[0], {1});
        tosat.bind(record.resultSymbol, {4, 5});
      }
    }
  }
};

// The first two actuals are equal Bool/BV constants in both applications;
// the latter two collide through a symbol/constant equality.  This reaches
// constant handling through the checker and adapter instead of exposing the
// encoder's private equality helper to the test.
struct ConstantOperandFixture
{
  STPMgr manager;
  SubstitutionMap substitutions;
  Simplifier simplifier;
  ArrayTransformer transformer;
  AbsRefine_CounterExample counterexample;
  UFContext* context;
  const UFDecl* function;
  ASTNode predicate;
  ASTNode x;
  ASTNode left;
  ASTNode right;
  LoweredApplicationView view;
  LoweredApplicationView persistentView;
  RecordingToSAT tosat;

  ConstantOperandFixture()
      : substitutions(&manager), simplifier(&manager, &substitutions),
        transformer(&manager, &simplifier),
        counterexample(&manager, &simplifier, &transformer), context(NULL),
        function(NULL), tosat(&manager)
  {
    manager.UserFlags.enable_uninterpreted_functions = true;
    context = manager.getUFContext();
    std::string diagnostic;
    const SourceSort boolean = SourceSort::boolean();
    const SourceSort bv2 = SourceSort::bitVector(2);
    function = context->declareFunction(
        "constant_operand_f", {boolean, bv2, boolean, bv2}, bv2,
        &diagnostic);
    EXPECT_NE(nullptr, function) << diagnostic;

    predicate = manager.CreateSourceSymbol("constant_operand_p", boolean);
    x = manager.CreateSourceSymbol("constant_operand_x", bv2);
    const ASTNode one = manager.CreateBVConst(2, 1);
    left = context->apply(function, {manager.ASTTrue, one, predicate, x},
                          &diagnostic);
    right = context->apply(
        function, {manager.ASTTrue, one, manager.ASTTrue, one}, &diagnostic);
    const ASTNode root = manager.defaultNodeFactory->CreateNode(
        NOT, manager.defaultNodeFactory->CreateNode(EQ, left, right));
    UFLowering lowerer(&manager);
    view = lowerer.lowerCompletedRoot(root, UFSolveScope::batch(11));
    persistentView = lowerer.lowerCompletedRoot(
        root, UFSolveScope::persistent(11, 7));

    EXPECT_EQ(2u, view.applications.size());
    EXPECT_EQ(2u, persistentView.applications.size());
    counterexample.InsertIntoCounterExampleMap(predicate, manager.ASTTrue);
    counterexample.InsertIntoCounterExampleMap(x, one);
    tosat.bind(predicate, {0});
    tosat.bind(x, {1, 2});
    populate(view);
    populate(persistentView);
  }

  void populate(const LoweredApplicationView& applicationView)
  {
    for (const LoweredApplicationRecord& record : applicationView.applications)
    {
      const bool isLeft = record.durableHandle == left;
      counterexample.InsertIntoCounterExampleMap(
          record.resultSymbol, manager.CreateBVConst(2, isLeft ? 0 : 2));
      if (isLeft)
        tosat.bind(record.resultSymbol, {3, 4});
      else
        tosat.bind(record.resultSymbol, {5, 6});
    }
  }
};

// One exact-identical BV premise and one genuine BV premise.  The former
// must disappear before CNF construction, while the latter is reusable from
// the adapter's query-local equality cache.
struct IdenticalPremiseFixture
{
  STPMgr manager;
  SubstitutionMap substitutions;
  Simplifier simplifier;
  ArrayTransformer transformer;
  AbsRefine_CounterExample counterexample;
  UFContext* context;
  const UFDecl* function;
  ASTNode shared;
  ASTNode x;
  ASTNode y;
  ASTNode left;
  ASTNode right;
  LoweredApplicationView view;
  RecordingToSAT tosat;

  IdenticalPremiseFixture()
      : substitutions(&manager), simplifier(&manager, &substitutions),
        transformer(&manager, &simplifier),
        counterexample(&manager, &simplifier, &transformer), context(NULL),
        function(NULL), tosat(&manager)
  {
    manager.UserFlags.enable_uninterpreted_functions = true;
    context = manager.getUFContext();
    std::string diagnostic;
    const SourceSort bv2 = SourceSort::bitVector(2);
    function = context->declareFunction("identical_premise_f", {bv2, bv2},
                                        bv2, &diagnostic);
    EXPECT_NE(nullptr, function) << diagnostic;
    shared = manager.CreateSourceSymbol("identical_premise_shared", bv2);
    x = manager.CreateSourceSymbol("identical_premise_x", bv2);
    y = manager.CreateSourceSymbol("identical_premise_y", bv2);
    left = context->apply(function, {shared, x}, &diagnostic);
    right = context->apply(function, {shared, y}, &diagnostic);
    const ASTNode root = manager.defaultNodeFactory->CreateNode(
        NOT, manager.defaultNodeFactory->CreateNode(EQ, left, right));
    UFLowering lowerer(&manager);
    view = lowerer.lowerCompletedRoot(root, UFSolveScope::batch(12));

    EXPECT_EQ(2u, view.applications.size());
    counterexample.InsertIntoCounterExampleMap(shared,
                                               manager.CreateBVConst(2, 0));
    counterexample.InsertIntoCounterExampleMap(x,
                                               manager.CreateBVConst(2, 3));
    counterexample.InsertIntoCounterExampleMap(y,
                                               manager.CreateBVConst(2, 3));
    tosat.bind(shared, {0, 1});
    tosat.bind(x, {2, 3});
    tosat.bind(y, {4, 5});
    for (const LoweredApplicationRecord& record : view.applications)
    {
      const bool isLeft = record.durableHandle == left;
      counterexample.InsertIntoCounterExampleMap(
          record.resultSymbol, manager.CreateBVConst(2, isLeft ? 1 : 2));
      if (isLeft)
        tosat.bind(record.resultSymbol, {6, 7});
      else
        tosat.bind(record.resultSymbol, {8, 9});
    }
  }
};

bool satisfies(const std::vector<std::vector<int>>& clauses,
               const std::vector<bool>& assignment)
{
  for (const std::vector<int>& clause : clauses)
  {
    bool clauseValue = false;
    for (const int literal : clause)
    {
      const unsigned variable = static_cast<unsigned>(literal) >> 1;
      const bool sign = (literal & 1) != 0;
      clauseValue = clauseValue || (assignment[variable] != sign);
    }
    if (!clauseValue)
      return false;
  }
  return true;
}

} // namespace

TEST(UFRefinement, CompletesACachedHelperUsedInBothPolarities)
{
  // The same equality can be a premise in one lemma and a conclusion in
  // another. Each use needs the opposite half of the helper definition, so
  // the second one has to complete what the first left out rather than
  // reuse the literal as it stands.
  //
  // Both applications of f take the same Bool argument here, so the argument
  // equality is the one the checker states as a premise, while the result
  // equality is the conclusion; the fixture's second, identical candidate
  // then reuses both from the cache. Whatever the order, the projection onto
  // the original variables must still be exactly the congruence implication,
  // which is what the exhaustive check below asserts.
  RefinementFixture fixture;
  UFBatchAdapter adapter(&fixture.manager);
  adapter.beginQuery(&fixture.batchView);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));

  RecordingSolver solver(6);
  adapter.encodePendingLemmas(solver, &fixture.tosat);
  const std::size_t afterFirst = solver.clauses().size();

  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  adapter.encodePendingLemmas(solver, &fixture.tosat);
  // A repeat in the same polarity completes nothing: one new implication.
  EXPECT_EQ(afterFirst + 1, solver.clauses().size());

  const unsigned helperCount = solver.nextVariable() - 6;
  for (unsigned original = 0; original < (1u << 6); ++original)
  {
    const bool argumentEqual =
        ((original >> 0) & 1u) == ((original >> 1) & 1u);
    const bool resultEqual =
        ((original >> 2) & 1u) == ((original >> 4) & 1u) &&
        ((original >> 3) & 1u) == ((original >> 5) & 1u);
    const bool expected = !argumentEqual || resultEqual;
    bool encoded = false;
    for (unsigned helpers = 0; helpers < (1u << helperCount); ++helpers)
    {
      std::vector<bool> assignment(solver.nextVariable(), false);
      for (unsigned bit = 0; bit < 6; ++bit)
        assignment[bit] = ((original >> bit) & 1u) != 0;
      for (unsigned bit = 0; bit < helperCount; ++bit)
        assignment[6 + bit] = ((helpers >> bit) & 1u) != 0;
      if (satisfies(solver.clauses(), assignment))
      {
        encoded = true;
        break;
      }
    }
    EXPECT_EQ(expected, encoded) << "original assignment " << original;
  }
}

TEST(UFRefinement, BatchCNFExactlyImplementsCongruenceImplication)
{
  RefinementFixture fixture;
  UFBatchAdapter adapter(&fixture.manager);
  adapter.beginQuery(&fixture.batchView);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  ASSERT_TRUE(adapter.hasPendingLemma());

  RecordingSolver solver(6);
  adapter.encodePendingLemmas(solver, &fixture.tosat);
  EXPECT_FALSE(adapter.hasPendingLemma());
  EXPECT_EQ(1u, adapter.lemmasEmitted());
  // Each helper is defined in the one polarity its use needs, which is half
  // of each definition. The premise appears negated, so its Bool XNOR gets
  // the two clauses for (l = r) -> q: 2. The conclusion appears positive, so
  // its two BV-bit XNORs get the two clauses each for q -> (l = r), and the
  // conjunction gets one clause per bit for q -> every bit: 4 + 2. The
  // semantic implication: 1.
  ASSERT_EQ(9u, solver.clauses().size());

  const unsigned helperCount = solver.nextVariable() - 6;
  for (unsigned original = 0; original < (1u << 6); ++original)
  {
    const bool argumentEqual =
        ((original >> 0) & 1u) == ((original >> 1) & 1u);
    const bool resultEqual =
        ((original >> 2) & 1u) == ((original >> 4) & 1u) &&
        ((original >> 3) & 1u) == ((original >> 5) & 1u);
    const bool expected = !argumentEqual || resultEqual;
    bool encoded = false;
    for (unsigned helpers = 0; helpers < (1u << helperCount); ++helpers)
    {
      std::vector<bool> assignment(solver.nextVariable(), false);
      for (unsigned bit = 0; bit < 6; ++bit)
        assignment[bit] = ((original >> bit) & 1u) != 0;
      for (unsigned bit = 0; bit < helperCount; ++bit)
        assignment[6 + bit] = ((helpers >> bit) & 1u) != 0;
      if (satisfies(solver.clauses(), assignment))
      {
        encoded = true;
        break;
      }
    }
    EXPECT_EQ(expected, encoded) << "original assignment " << original;
  }

  // A repeated candidate in one fresh query reuses both equality literals
  // and submits only the new candidate-blocking implication.
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  adapter.encodePendingLemmas(solver, &fixture.tosat);
  EXPECT_EQ(10u, solver.clauses().size());
  EXPECT_EQ(2u, adapter.lemmasEmitted());
}

TEST(UFRefinement, BatchCNFFoldsBoolAndBitVectorConstantOperands)
{
  ConstantOperandFixture fixture;
  UFBatchAdapter adapter(&fixture.manager);
  adapter.beginQuery(&fixture.view);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));

  RecordingSolver solver(7);
  adapter.encodePendingLemmas(solver, &fixture.tosat);

  // The two exact constant/constant premises disappear. p=true aliases p's
  // existing literal, while x=1 needs only the one clause that its negated
  // use requires of the conjunction of its two constant-adjusted bit
  // literals. The BV result equality, used positively, needs six. The
  // semantic implication one. Constants acquire no SAT vars.
  ASSERT_EQ(8u, solver.clauses().size());
  ASSERT_EQ(11u, solver.nextVariable());

  const unsigned helperCount = solver.nextVariable() - 7;
  for (unsigned original = 0; original < (1u << 7); ++original)
  {
    const bool predicate = ((original >> 0) & 1u) != 0;
    const unsigned x = ((original >> 1) & 1u) |
                       (((original >> 2) & 1u) << 1);
    const unsigned leftResult = ((original >> 3) & 1u) |
                                (((original >> 4) & 1u) << 1);
    const unsigned rightResult = ((original >> 5) & 1u) |
                                 (((original >> 6) & 1u) << 1);
    const bool expected = !predicate || x != 1 || leftResult == rightResult;
    bool encoded = false;
    for (unsigned helpers = 0; helpers < (1u << helperCount); ++helpers)
    {
      std::vector<bool> assignment(solver.nextVariable(), false);
      for (unsigned bit = 0; bit < 7; ++bit)
        assignment[bit] = ((original >> bit) & 1u) != 0;
      for (unsigned bit = 0; bit < helperCount; ++bit)
        assignment[7 + bit] = ((helpers >> bit) & 1u) != 0;
      if (satisfies(solver.clauses(), assignment))
      {
        encoded = true;
        break;
      }
    }
    EXPECT_EQ(expected, encoded) << "original assignment " << original;
  }
}

TEST(UFRefinement, RejectsMalformedPreencodedLeavesBeforeSATMutation)
{
  RefinementFixture fixture;
  UFBatchAdapter adapter(&fixture.manager);
  adapter.beginQuery(&fixture.batchView);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  ASSERT_TRUE(adapter.hasPendingLemma());

  // If validation regresses behind helper allocation or clause insertion,
  // this solver dies with a different diagnostic and the death check fails.
  RecordingSolver solver(6);
  solver.rejectMutation();
  // Corrupt a conclusion leaf, which is validated after every premise.  A
  // validate-as-you-encode implementation would already have allocated the
  // premise helper before it discovered any of these faults.
  const ASTNode leaf = fixture.batchView.applications[0].resultSymbol;
  ASSERT_EQ(SourceSort::bitVector(2), leaf.GetSourceSort());

  fixture.tosat.unbind(leaf);
  EXPECT_DEATH(adapter.encodePendingLemmas(solver, &fixture.tosat),
               "not registered before the first candidate");

  fixture.tosat.bind(leaf, {2});
  EXPECT_DEATH(adapter.encodePendingLemmas(solver, &fixture.tosat),
               "wrong-width SAT mapping");

  fixture.tosat.bind(leaf, {2, ~0u});
  EXPECT_DEATH(adapter.encodePendingLemmas(solver, &fixture.tosat),
               "unencoded SAT bit");
}

TEST(UFRefinement, BatchCNFEliminatesIdenticalPremiseAndReusesCache)
{
  IdenticalPremiseFixture fixture;
  UFBatchAdapter adapter(&fixture.manager);
  adapter.beginQuery(&fixture.view);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));

  RecordingSolver solver(10);
  adapter.encodePendingLemmas(solver, &fixture.tosat);
  // Only x=y and the result equality remain: two BV2 XNOR/conjunction
  // bundles of three helpers each, defined in the one polarity each use
  // needs -- five clauses for the negated premise, six for the positive
  // conclusion -- plus the implication.
  EXPECT_EQ(12u, solver.clauses().size());
  EXPECT_EQ(16u, solver.nextVariable());

  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  adapter.encodePendingLemmas(solver, &fixture.tosat);
  // Both surviving equality literals are cache hits, and each is reused in
  // the same polarity it was defined in.  The repeat contributes just another
  // candidate-blocking implication and no new helper variable.
  EXPECT_EQ(13u, solver.clauses().size());
  EXPECT_EQ(16u, solver.nextVariable());
}


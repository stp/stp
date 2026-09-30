#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{
TEST(IncrementalAssumptionOrigins, SharedConjunctsKeepOneSourceOccurrence)
{
  STPMgr bm;
  SubstitutionMap sm(&bm);
  Simplifier simp(&bm, &sm);
  ArrayTransformer at(&bm, &simp);
  AbsRefine_CounterExample ce(&bm, &simp, &at);
  IncrementalSolver inc(&bm, &ce, &simp, &at);
  NodeFactory* nf = bm.defaultNodeFactory;
  const ASTNode p = bm.CreateSymbol("p", 0, 0);
  const ASTNode q = bm.CreateSymbol("q", 0, 0);
  const ASTNode r = bm.CreateSymbol("r", 0, 0);
  const ASTNode negative = nf->CreateNode(NOT, p);
  const ASTVec sources{nf->CreateNode(AND, p, q), p, negative, r};
  // Even if a caller's conjunction already collapsed, the source snapshot
  // retains both sides of the contradiction and their occurrence identities.
  const ASTVec stack{bm.ASTTrue, nf->CreateNode(AND, sources)};
  ASSERT_EQ(SOLVER_UNSATISFIABLE, inc.checkSat(stack, true, false, &sources));
  EXPECT_EQ((std::vector<size_t>{0, 2}), inc.lastUnsatAssumptionIndices());

  const ASTVec next{r, negative};
  ASSERT_EQ(SOLVER_UNSATISFIABLE,
            inc.checkSat(ASTVec{p, nf->CreateNode(AND, next)}, true, false, &next));
  EXPECT_EQ((std::vector<size_t>{1}), inc.lastUnsatAssumptionIndices());
}

TEST(IncrementalAssumptionOrigins, TrueAndFalseRetainInputPositions)
{
  STPMgr bm;
  SubstitutionMap sm(&bm);
  Simplifier simp(&bm, &sm);
  ArrayTransformer at(&bm, &simp);
  AbsRefine_CounterExample ce(&bm, &simp, &at);
  IncrementalSolver inc(&bm, &ce, &simp, &at);
  const ASTVec sources{bm.ASTTrue, bm.ASTFalse, bm.ASTFalse};
  ASSERT_EQ(SOLVER_UNSATISFIABLE,
            inc.checkSat(ASTVec{bm.ASTTrue, bm.ASTFalse}, true, false, &sources));
  EXPECT_EQ((std::vector<size_t>{1}), inc.lastUnsatAssumptionIndices());
  const ASTVec none;
  ASSERT_EQ(SOLVER_UNSATISFIABLE,
            inc.checkSat(ASTVec{bm.ASTFalse, bm.ASTTrue}, true, false, &none));
  EXPECT_TRUE(inc.lastUnsatAssumptionIndices().empty());
}

TEST(IncrementalAssumptionOrigins, TheorySelectorsDoNotNarrowTheScopeCache)
{
  STPMgr bm;
  bm.UserFlags.enable_array_equality = true;
  bm.UserFlags.array_eager_budget = 0;
  SubstitutionMap sm(&bm);
  Simplifier simp(&bm, &sm);
  ArrayTransformer at(&bm, &simp);
  AbsRefine_CounterExample ce(&bm, &simp, &at);
  IncrementalSolver inc(&bm, &ce, &simp, &at);
  NodeFactory* nf = bm.defaultNodeFactory;
  const ASTNode a = bm.CreateSymbol("a", 4, 8);
  const ASTNode b = bm.CreateSymbol("b", 4, 8);
  const ASTNode i = bm.CreateSymbol("i", 0, 4);
  const ASTNode irrelevant = bm.CreateSymbol("irrelevant", 0, 0);
  const ASTNode equal = nf->CreateNode(ARRAY_EQ, a, b);
  const ASTNode different = nf->CreateNode(NOT, nf->CreateNode(
      EQ, nf->CreateTerm(READ, 8, a, i), nf->CreateTerm(READ, 8, b, i)));
  const ASTVec sources{different, irrelevant};
  ASSERT_EQ(SOLVER_UNSATISFIABLE, inc.checkSat(
      ASTVec{bm.ASTTrue, equal, nf->CreateNode(AND, sources)}, true, false, &sources));
  EXPECT_TRUE(inc.lastUnsatHasAssumptionGranularity());
  EXPECT_EQ((std::vector<size_t>{0}), inc.lastUnsatAssumptionIndices());
  EXPECT_EQ((std::vector<size_t>{1, 2}), inc.lastUnsatCoreLevels());

  ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(ASTVec{bm.ASTTrue, equal}));
  EXPECT_FALSE(inc.lastUnsatHasAssumptionGranularity());

  const ASTVec none;
  ASSERT_EQ(SOLVER_UNSATISFIABLE, inc.checkSat(
      ASTVec{bm.ASTTrue, nf->CreateNode(AND, equal, different), bm.ASTTrue},
      true, false, &none));
  EXPECT_TRUE(inc.lastUnsatHasAssumptionGranularity());
  EXPECT_TRUE(inc.lastUnsatAssumptionIndices().empty());
}
} // namespace

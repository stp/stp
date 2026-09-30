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
} // namespace

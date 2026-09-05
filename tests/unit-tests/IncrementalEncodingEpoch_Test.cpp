/********************************************************************
 * A relief rebuild must reclaim the complete historical encoding store,
 * not merely replace the SAT backend while retaining its AIG and memos.
 ********************************************************************/

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <sstream>

using namespace stp;

namespace
{

TEST(IncrementalEncodingEpoch, ReliefReleasesAigAndSemanticHighWaterState)
{
  STPMgr mgr;
  // Reclamation belongs to the minimal correctness/resource core; it must not
  // depend on any of the optional preparation or backend policies.
  mgr.UserFlags.incremental_core_only = true;
  mgr.UserFlags.incremental_reencode_limit = 1;
  mgr.UserFlags.incremental_base_resimplify_limit = 0;

  SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  ArrayTransformer at(&mgr, &simp);
  AbsRefine_CounterExample ce(&mgr, &simp, &at);
  IncrementalSolver inc(&mgr, &ce, &simp, &at);

  NodeFactory* nf = mgr.defaultNodeFactory;
  const ASTNode x = mgr.CreateSymbol("epoch_x", 0, 8);
  const ASTNode base = nf->CreateNode(
      BVLT, x, mgr.CreateBVConst(8, 16));

  size_t highAigNodes = 0;
  size_t highRoots = 0;
  size_t highSemanticEntries = 0;
  bool rotated = false;
  ASTVec liveStack;

  for (unsigned round = 0; round < 64 && !rotated; ++round)
  {
    std::ostringstream name;
    name << "epoch_y_" << round;
    const std::string symbolName = name.str();
    const ASTNode y = mgr.CreateSymbol(symbolName.c_str(), 0, 8);
    const ASTNode square = nf->CreateTerm(BVMULT, 8, y, y);
    const ASTNode pushed = nf->CreateNode(
        BVGT, square, mgr.CreateBVConst(8, (round & 1) ? 39 : 3));
    liveStack = ASTVec{base, pushed};

    ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(liveStack));
    const IncrementalSolver::EncodingEpochStats stats =
        inc.encodingEpochStatsForTesting();
    if (stats.generation == 0)
    {
      highAigNodes = std::max(highAigNodes, stats.aigAndNodes);
      highRoots = std::max(highRoots, stats.rootEncodings);
      highSemanticEntries =
          std::max(highSemanticEntries, stats.semanticCacheEntries);
      continue;
    }

    rotated = true;
    EXPECT_EQ(1u, stats.generation);
    EXPECT_LT(stats.aigAndNodes, highAigNodes);
    EXPECT_LT(stats.rootEncodings, highRoots);
    EXPECT_LT(stats.semanticCacheEntries, highSemanticEntries);

    // Persistence remains the ordinary case inside the new epoch: an
    // identical stack neither rotates again nor grows its AIG/root stores.
    const IncrementalSolver::EncodingEpochStats afterRelief = stats;
    ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(liveStack));
    const IncrementalSolver::EncodingEpochStats repeated =
        inc.encodingEpochStatsForTesting();
    EXPECT_EQ(afterRelief.generation, repeated.generation);
    EXPECT_EQ(afterRelief.aigAndNodes, repeated.aigAndNodes);
    EXPECT_EQ(afterRelief.rootEncodings, repeated.rootEncodings);
  }

  EXPECT_TRUE(rotated);
}

TEST(IncrementalEncodingEpoch, SemanticOnlyRootChurnAlsoTriggersRelief)
{
  STPMgr mgr;
  mgr.UserFlags.incremental_reencode_limit = 0;
  mgr.UserFlags.incremental_semantic_cache_limit = 8;
  mgr.UserFlags.incremental_base_resimplify_limit = 0;

  SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  ArrayTransformer at(&mgr, &simp);
  AbsRefine_CounterExample ce(&mgr, &simp, &at);
  IncrementalSolver inc(&mgr, &ce, &simp, &at);

  NodeFactory* nf = mgr.defaultNodeFactory;
  const ASTNode base = mgr.CreateSymbol("epoch_true_base", 0, 0);
  bool rotated = false;

  // Every distinct raw root collapses to TRUE under the permanent base
  // definition, so the SAT backend stays below the configured variable
  // threshold while root/fragment/preparation keys would otherwise grow
  // forever. The root working-set ratio must rotate the complete epoch.
  for (unsigned round = 0; round < 64 && !rotated; ++round)
  {
    std::ostringstream name;
    name << "epoch_unused_" << round;
    const std::string symbolName = name.str();
    const ASTNode unused = mgr.CreateSymbol(symbolName.c_str(), 0, 0);
    const ASTNode pushed = nf->CreateNode(OR, base, unused);
    ASSERT_EQ(SOLVER_SATISFIABLE,
              inc.checkSat(ASTVec{base, pushed}, true));

    const IncrementalSolver::EncodingEpochStats stats =
        inc.encodingEpochStatsForTesting();
    if (stats.generation == 0)
      continue;
    rotated = true;
    EXPECT_LT(stats.bitBlastedSymbols, 8u);
    EXPECT_LT(stats.rootEncodings, 8u);
  }

  EXPECT_TRUE(rotated);
}

} // namespace

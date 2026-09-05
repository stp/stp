/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "Incremental/IncrementalLifetimeState.h"
#include "stp/STPManager/STPManager.h"
#include <gtest/gtest.h>

using namespace stp;

namespace
{

TEST(IncrementalLifetimeState, symbol_map_validity_keeps_its_storage)
{
  STPMgr mgr;
  const ASTNode symbol = mgr.CreateSymbol("symbol-map-cache", 0, 8);
  IncrementalSymbolMapCache cache;
  cache.storage()[symbol].push_back(7);
  cache.markCurrent(3);

  EXPECT_TRUE(cache.validFor(3));
  EXPECT_FALSE(cache.validFor(4));

  cache.invalidate();
  EXPECT_FALSE(cache.validFor(3));
  EXPECT_EQ(1u, cache.storage().count(symbol));

  cache.releaseStorage();
  EXPECT_TRUE(cache.storage().empty());
  EXPECT_FALSE(cache.validFor(3));
}

TEST(IncrementalLifetimeState, pending_live_cone_resets_atomically)
{
  IncrementalPendingLiveCone pending;
  std::vector<Aig_Obj_t*> roots(2, nullptr);
  pending.replace(roots, 5, 11);

  EXPECT_TRUE(pending.active());
  EXPECT_TRUE(roots.empty());
  EXPECT_EQ(2u, pending.roots().size());
  EXPECT_EQ(5u, pending.permanentRoots());
  EXPECT_EQ(11u, pending.nonStructural());

  pending.clear();
  EXPECT_FALSE(pending.active());
  EXPECT_TRUE(pending.roots().empty());
  EXPECT_EQ(0u, pending.permanentRoots());
  EXPECT_EQ(0u, pending.nonStructural());
}

TEST(IncrementalLifetimeState, semantic_epoch_releases_roots_and_high_water)
{
  STPMgr mgr;
  const ASTNode root = mgr.CreateSymbol("semantic-epoch-root", 0, 8);
  IncrementalSemanticEpochAccounting accounting;

  accounting.charge(root, 1);
  accounting.charge(root, 1);
  EXPECT_EQ(1u, accounting.retainedRootCount());

  ASTVec rawStack(1, root);
  ASTVec encodedRoots;
  accounting.stage(rawStack, encodedRoots);
  EXPECT_FALSE(accounting.reliefReached(1));
  EXPECT_EQ(1u, accounting.maxLiveNodeCount());
  EXPECT_EQ(1u, accounting.lastRetainedNodeCount());

  accounting.releaseStorage();
  EXPECT_EQ(0u, accounting.retainedRootCount());
  EXPECT_EQ(0u, accounting.maxLiveNodeCount());
  EXPECT_EQ(0u, accounting.lastRetainedNodeCount());
  EXPECT_FALSE(accounting.reliefReached(1));
}

} // namespace

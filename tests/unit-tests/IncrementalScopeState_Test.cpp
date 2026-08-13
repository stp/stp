// Scope identity, consumer cursors and preprocessing commit ownership.

#include "stp/Incremental/IncrementalScopeState.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

TEST(IncrementalScopeState, ReconcileVersionsChangedSuffixesAndTracksStability)
{
  STPMgr mgr;
  IncrementalScopeState scopes;
  const ASTNode a = mgr.CreateSymbol("scope_a", 0, 0);
  const ASTNode b = mgr.CreateSymbol("scope_b", 0, 0);
  const ASTNode c = mgr.CreateSymbol("scope_c", 0, 0);

  ASTVec first{a, b};
  EXPECT_EQ(0u, scopes.reconcile(first).commonPrefix);
  const uint64_t baseId = scopes.levelAt(0).id;
  const uint64_t oldTopId = scopes.levelAt(1).id;
  EXPECT_EQ(0u, scopes.stableSolves(0));

  EXPECT_EQ(2u, scopes.reconcile(first).commonPrefix);
  EXPECT_EQ(1u, scopes.stableSolves(0));
  EXPECT_EQ(1u, scopes.stableSolves(1));

  ASTVec changed{a, c};
  EXPECT_EQ(1u, scopes.reconcile(changed).commonPrefix);
  EXPECT_EQ(baseId, scopes.levelAt(0).id);
  EXPECT_NE(oldTopId, scopes.levelAt(1).id);
  EXPECT_EQ(0u, scopes.stableSolves(1));
}

TEST(IncrementalScopeState, ConsumerCursorSurvivesAnUnsynchronisedRoute)
{
  STPMgr mgr;
  IncrementalScopeState scopes;
  const ASTNode a = mgr.CreateSymbol("cursor_a", 0, 0);
  const ASTNode b = mgr.CreateSymbol("cursor_b", 0, 0);
  const ASTNode c = mgr.CreateSymbol("cursor_c", 0, 0);

  scopes.reconcile(ASTVec{a, b});
  scopes.markCbpFed(0);
  scopes.markCbpFed(1);
  EXPECT_EQ(2u, scopes.cbpFedCommonPrefix());

  // Models an exact-stack route: the frontend snapshot changes, but that
  // route does not touch CBP. The processed cursor must retain the old view
  // so the next ordinary route sees and rolls back the divergent suffix.
  scopes.reconcile(ASTVec{a, c});
  EXPECT_EQ(1u, scopes.cbpFedCommonPrefix());
  EXPECT_EQ(2u, scopes.cbpFedDepth());
  scopes.rollbackCbpFedTo(1);
  EXPECT_EQ(1u, scopes.cbpFedDepth());
  scopes.markCbpFed(1);
  EXPECT_EQ(2u, scopes.cbpFedCommonPrefix());
}

TEST(IncrementalScopeState, NewScopeIdentityCanStillReuseContentMemo)
{
  STPMgr mgr;
  IncrementalScopeState scopes;
  const ASTNode a = mgr.CreateSymbol("memo_a", 0, 0);
  const ASTNode b = mgr.CreateSymbol("memo_b", 0, 0);
  const ASTNode c = mgr.CreateSymbol("memo_c", 0, 0);

  scopes.reconcile(ASTVec{a, b});
  scopes.markCbpFed(0);
  scopes.markCbpFed(1);
  scopes.startCbpMemo(0);
  scopes.startCbpMemo(1);

  // Observe a replacement scope and then an identical re-push of b. Its
  // level identity is new, so the processed engine prefix must roll back;
  // the raw-content memo is a separate cache and remains reusable.
  scopes.reconcile(ASTVec{a, c});
  scopes.reconcile(ASTVec{a, b});
  EXPECT_EQ(1u, scopes.cbpFedCommonPrefix());
  EXPECT_EQ(2u, scopes.trimCbpMemoToCurrent());
}

TEST(IncrementalScopeState, PreprocessingCommitsFormulaAndModelStateTogether)
{
  STPMgr mgr;
  IncrementalScopeState scopes;
  const ASTNode raw = mgr.CreateSymbol("transaction_raw", 0, 0);
  const ASTNode prepared = mgr.CreateSymbol("transaction_prepared", 0, 0);
  const ASTNode x = mgr.CreateSymbol("transaction_x", 0, 8);
  const ASTNode value = mgr.CreateBVConst(8, 7);
  scopes.reconcile(ASTVec{mgr.ASTTrue, raw});

  PreprocessingTransaction transaction(PreprocessingMode::PerLevel, raw);
  transaction.conjuncts.push_back(prepared);
  transaction.addElimination(x, value);
  scopes.commitLevel(1, transaction);

  ASSERT_EQ(1u, scopes.activeSemanticKeys().size());
  EXPECT_EQ(prepared, scopes.activeSemanticKeys()[0]);
  ASSERT_EQ(1u, scopes.activeEliminations().size());
  EXPECT_EQ(x, scopes.activeEliminations()[0].symbol);
  EXPECT_TRUE(scopes.activeEliminatedVariables().count(x));

  // A new check begins with no committed semantic output. A caller cannot
  // accidentally retain the model half of the old transaction while using a
  // new formula half.
  scopes.reconcile(ASTVec{mgr.ASTTrue, raw});
  EXPECT_TRUE(scopes.activeSemanticKeys().empty());
  EXPECT_TRUE(scopes.activeEliminations().empty());
}

TEST(IncrementalScopeState, PromotionIsOwnedByThePreparedLevel)
{
  STPMgr mgr;
  IncrementalScopeState scopes;
  const ASTNode base = mgr.ASTTrue;
  const ASTNode a = mgr.CreateSymbol("promotion_a", 0, 0);
  const ASTNode b = mgr.CreateSymbol("promotion_b", 0, 0);
  scopes.reconcile(ASTVec{base, a, b});

  ASTVec prepared{a};
  scopes.promote(1, prepared);
  EXPECT_EQ(1u, scopes.promotedDepth());
  EXPECT_FALSE(scopes.promotedConjunctsChanged(1, prepared));

  scopes.notePromotionDrift();
  const IncrementalScopeState::ReconcileResult same =
      scopes.reconcile(ASTVec{base, a, b});
  EXPECT_TRUE(same.promotedPrefixRetracted);
  EXPECT_EQ(0u, scopes.promotedDepth());
}

TEST(IncrementalScopeState, EpochReleasePreservesOnlyTheLiveRawLedger)
{
  STPMgr mgr;
  IncrementalScopeState scopes;
  const ASTNode base = mgr.ASTTrue;
  const ASTNode a = mgr.CreateSymbol("epoch_a", 0, 0);
  const ASTNode b = mgr.CreateSymbol("epoch_b", 0, 0);

  scopes.reconcile(ASTVec{base, a, b});
  scopes.reconcile(ASTVec{base, a});
  const uint64_t baseId = scopes.levelAt(0).id;
  const uint64_t topId = scopes.levelAt(1).id;
  const size_t baseStability = scopes.stableSolves(0);

  scopes.markCbpFed(0);
  scopes.markCbpFed(1);
  scopes.startCbpMemo(0);
  scopes.startCbpMemo(1);
  scopes.releaseEpochStorage();

  ASSERT_EQ(2u, scopes.size());
  EXPECT_EQ(baseId, scopes.levelAt(0).id);
  EXPECT_EQ(topId, scopes.levelAt(1).id);
  EXPECT_EQ(baseStability, scopes.stableSolves(0));
  EXPECT_EQ(0u, scopes.cbpFedDepth());
  EXPECT_EQ(0u, scopes.cbpMemoDepth());
  EXPECT_TRUE(scopes.activeSemanticKeys().empty());
  EXPECT_TRUE(scopes.activeEliminations().empty());
}

} // namespace

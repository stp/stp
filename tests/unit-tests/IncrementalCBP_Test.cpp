/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "stp/Incremental/IncrementalCBP.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

ASTNode equality(STPMgr& mgr, const ASTNode& a, const ASTNode& b)
{
  return mgr.defaultNodeFactory->CreateNode(EQ, a, b);
}

TEST(IncrementalCBP, rollback_restores_existing_fixed_bits)
{
  STPMgr mgr;
  IncrementalCBP cbp(&mgr, mgr.defaultNodeFactory);
  const ASTNode x = mgr.CreateSymbol("x", 0, 128);
  const ASTNode y = mgr.CreateSymbol("y", 0, 128);
  const ASTNode z = mgr.CreateSymbol("z", 0, 128);
  const ASTNode sum = mgr.defaultNodeFactory->CreateTerm(BVPLUS, 128, x, y);

  ASSERT_TRUE(cbp.feedLevel(equality(mgr, z, sum)));
  ASSERT_TRUE(cbp.feedLevel(equality(mgr, x, mgr.CreateBVConst(128, 1))));
  ASSERT_TRUE(cbp.feedLevel(equality(mgr, y, mgr.CreateBVConst(128, 2))));
  EXPECT_EQ(mgr.CreateBVConst(128, 3), cbp.constantOf(z));
  EXPECT_EQ(3u, cbp.levelCount());

  const IncrementalCBP::RollbackStats rolled = cbp.rollbackTo(2);
  EXPECT_EQ(1u, rolled.levels);
  EXPECT_TRUE(cbp.constantOf(y).IsNull());
  EXPECT_TRUE(cbp.constantOf(z).IsNull());
  EXPECT_EQ(mgr.CreateBVConst(128, 1), cbp.constantOf(x));

  ASSERT_TRUE(cbp.feedLevel(equality(mgr, y, mgr.CreateBVConst(128, 4))));
  EXPECT_EQ(mgr.CreateBVConst(128, 5), cbp.constantOf(z));
}

TEST(IncrementalCBP, rollback_clears_conflict_and_queued_work)
{
  STPMgr mgr;
  IncrementalCBP cbp(&mgr, mgr.defaultNodeFactory);
  const ASTNode x = mgr.CreateSymbol("x", 0, 8);
  const ASTNode y = mgr.CreateSymbol("y", 0, 8);

  ASSERT_TRUE(cbp.feedLevel(equality(mgr, x, mgr.CreateBVConst(8, 1))));
  ASSERT_FALSE(cbp.feedLevel(equality(mgr, x, mgr.CreateBVConst(8, 2))));
  EXPECT_TRUE(cbp.inConflict());

  // A feed below an already conflicting prefix is still a level transaction:
  // popping it must retain the parent conflict, and popping the refuting level
  // must clear it.
  ASSERT_FALSE(cbp.feedLevel(equality(mgr, y, mgr.CreateBVConst(8, 3))));
  EXPECT_EQ(3u, cbp.levelCount());
  EXPECT_EQ(1u, cbp.rollbackTo(2).levels);
  EXPECT_TRUE(cbp.inConflict());
  EXPECT_EQ(1u, cbp.rollbackTo(1).levels);
  EXPECT_FALSE(cbp.inConflict());
  EXPECT_EQ(mgr.CreateBVConst(8, 1), cbp.constantOf(x));

  const ASTNode plusOne =
      mgr.defaultNodeFactory->CreateTerm(BVPLUS, 8, x, mgr.CreateBVConst(8, 1));
  ASSERT_TRUE(cbp.feedLevel(equality(mgr, y, plusOne)));
  EXPECT_EQ(mgr.CreateBVConst(8, 2), cbp.constantOf(y));
}

TEST(IncrementalCBP, rollback_restores_multiplication_state)
{
  STPMgr mgr;
  IncrementalCBP cbp(&mgr, mgr.defaultNodeFactory);
  const ASTNode x = mgr.CreateSymbol("x", 0, 8);
  const ASTNode z = mgr.CreateSymbol("z", 0, 8);
  const ASTNode product =
      mgr.defaultNodeFactory->CreateTerm(BVMULT, 8, x, mgr.CreateBVConst(8, 3));

  ASSERT_TRUE(cbp.feedLevel(equality(mgr, z, product)));
  ASSERT_TRUE(cbp.feedLevel(equality(mgr, x, mgr.CreateBVConst(8, 2))));
  EXPECT_EQ(mgr.CreateBVConst(8, 6), cbp.constantOf(z));

  EXPECT_EQ(1u, cbp.rollbackTo(1).levels);
  EXPECT_TRUE(cbp.constantOf(x).IsNull());
  EXPECT_TRUE(cbp.constantOf(z).IsNull());

  ASSERT_TRUE(cbp.feedLevel(equality(mgr, x, mgr.CreateBVConst(8, 4))));
  EXPECT_EQ(mgr.CreateBVConst(8, 12), cbp.constantOf(z));
}

TEST(IncrementalCBP, an_already_false_level_is_a_conflict)
{
  STPMgr mgr;
  IncrementalCBP cbp(&mgr, mgr.defaultNodeFactory);

  EXPECT_FALSE(cbp.feedLevel(mgr.ASTFalse));
  EXPECT_TRUE(cbp.inConflict());
  EXPECT_EQ(1u, cbp.levelCount());
  EXPECT_EQ(1u, cbp.rollbackTo(0).levels);
  EXPECT_FALSE(cbp.inConflict());
}

} // namespace

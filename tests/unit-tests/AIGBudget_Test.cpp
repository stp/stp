/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/STPManager/STPManager.h"
#include <gtest/gtest.h>

#include <string>
#include <vector>

using namespace stp;

namespace
{

// The cap lives on BBNodeManagerAIG, so it is exercised here directly: the
// end-to-end wiring (option, UserFlags field, abandonment verdict) is what
// tests/query-files/misc-tests/aig-node-budget.smt2 covers.
class AIGBudgetTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  BBNodeManagerAIG aig;
  unsigned counter = 0;

  BBNodeAIG input()
  {
    const ASTNode s =
        mgr.CreateSymbol(("v" + std::to_string(counter++)).c_str(), 0, 1);
    return aig.CreateSymbol(s, 0);
  }

  // One AND gate over two fresh inputs, so the AND-gate count rises by
  // exactly one per call and never strashes against an earlier node.
  void makeOneAnd()
  {
    BBNodeAIG a = input(), b = input();
    std::vector<BBNodeAIG> children{a, b};
    aig.CreateNode(AND, children);
  }

  int andNodes() const { return aig.aigMgr->nObjs[AIG_OBJ_AND]; }
};

TEST_F(AIGBudgetTest, NoBudgetNeverThrows)
{
  EXPECT_EQ(aig.nodeBudget, -1); // the default, and the "no limit" sentinel
  for (int i = 0; i < 100; i++)
    ASSERT_NO_THROW(makeOneAnd());
  EXPECT_EQ(andNodes(), 100);
}

// -1 is no limit and 0 is none at all, matching --max-num-confl/--max-time.
// The two sentinels are one sign apart, so the test that they do opposite
// things is the one that catches a `> 0` guard creeping back in.
TEST_F(AIGBudgetTest, ZeroBudgetPermitsNoGateAtAll)
{
  aig.nodeBudget = 0;
  EXPECT_THROW(makeOneAnd(), AIGBudgetExhausted);
}

// The budget is a count of AND gates, so N of them must be allowed to exist:
// this pins that the cap is `>` and not `>=`, which no assertion phrased in
// terms of the throw itself can distinguish.
TEST_F(AIGBudgetTest, BudgetPermitsExactlyItsOwnCount)
{
  aig.nodeBudget = 8;
  for (int i = 0; i < 8; i++)
    ASSERT_NO_THROW(makeOneAnd());
  EXPECT_EQ(andNodes(), 8);
  EXPECT_THROW(makeOneAnd(), AIGBudgetExhausted);
}

TEST_F(AIGBudgetTest, BudgetExhaustedThrows)
{
  aig.nodeBudget = 5;
  EXPECT_THROW(
      {
        for (int i = 0; i < 1000; i++)
          makeOneAnd();
      },
      AIGBudgetExhausted);
}

// One CreateNode() can build a whole fan-in tower before checkBudget() runs,
// so the reported count is the count actually reached rather than the cap.
// Here the tower is one gate wide, so it is the cap plus one exactly.
TEST_F(AIGBudgetTest, ExhaustedNodeCountIsTheCountReached)
{
  aig.nodeBudget = 3;
  try
  {
    for (int i = 0; i < 1000; i++)
      makeOneAnd();
    FAIL() << "should have thrown";
  }
  catch (const AIGBudgetExhausted& e)
  {
    EXPECT_EQ(e.nodeCount, 4);
    EXPECT_EQ(e.nodeCount, andNodes());
    EXPECT_STREQ(e.what(), "AIG node budget exhausted");
  }
}

// A wide operator checks its budget once, after its whole fan-in tower: an
// 8-input AND builds 7 gates from a cap of 1. The overshoot is bounded by
// the width of one operator, and this is the test that says so out loud.
TEST_F(AIGBudgetTest, OvershootIsBoundedByOneOperatorsFanIn)
{
  aig.nodeBudget = 1;
  std::vector<BBNodeAIG> children;
  for (int i = 0; i < 8; i++)
    children.push_back(input());

  try
  {
    aig.CreateNode(AND, children);
    FAIL() << "should have thrown";
  }
  catch (const AIGBudgetExhausted& e)
  {
    EXPECT_EQ(e.nodeCount, 7);
  }
}

} // namespace

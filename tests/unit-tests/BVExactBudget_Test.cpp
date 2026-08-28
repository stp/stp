/***********
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
**********************/

// What the refinement does when the AIG node budget will not build the
// circuit it wants.
//
// --aig-node-budget is a memory guard, and the exact encoding an abstraction
// escalates to is the largest circuit the refinement ever builds, so it is the
// one the guard refuses first. The bounded value-instantiation tier has then
// done all the work its policy permits; replacing the refused exact tier with
// unbounded operand-pair enumeration would make the memory guard trigger an
// exponential fallback. The refusal is therefore an explicit Unknown result.
#include "stp/ToSat/BVAbstractionRefiner.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <memory>
#include <vector>

using namespace stp;

namespace
{

unsigned refinedCount(const AbstractionRefinementResult& result)
{
  EXPECT_TRUE(result.madeProgress());
  return result.refined;
}

void appendTermRecord(BVAbstractionRefiner& refiner,
                      BVTermAbstraction record)
{
  static uint64_t nextId = 1;
  record.id = BVAbstractionId(nextId++);
  refiner.appendTerm(record);
}

const unsigned WIDTH = 32;

// Small enough that a 32-bit multiplier does not fit, large enough that
// nothing else here needs one. The refusal is what is being tested, so the
// number only has to be on the refusing side of that circuit.
const int64_t REFUSING_BUDGET = 200;

class BVExactBudgetTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  std::unique_ptr<SATSolver> makeSolver()
  {
    return std::unique_ptr<SATSolver>(createSATSolver(mgr.UserFlags));
  }

  std::vector<unsigned> makeVars(SATSolver& solver)
  {
    std::vector<unsigned> vars(WIDTH);
    for (unsigned i = 0; i < WIDTH; ++i)
    {
      vars[i] = solver.newVar();
      solver.setFrozen(vars[i]);
    }
    return vars;
  }

  void pin(SATSolver& solver, const std::vector<unsigned>& vars,
           uint64_t value)
  {
    SATSolver::vec_literals unit;
    for (unsigned i = 0; i < WIDTH; ++i)
    {
      unit.clear();
      unit.push(SATSolver::mkLit(vars[i], ((value >> i) & 1u) == 0));
      solver.addClause(unit);
    }
  }
};

} // namespace

// One record, one allowance, and a budget that will not build its circuit.
//
// The first round spends the allowance on a blocking lemma. The second wants
// to escalate and is refused. It must say Unknown rather than returning the
// old zero-refinement value (which meant faithful), or silently beginning an
// exponential enumeration of all remaining operand pairs.
TEST_F(BVExactBudgetTest, ARefusedMandatoryEscalationIsExplicitlyUnknown)
{
  mgr.UserFlags.aig_node_budget = REFUSING_BUDGET;
  mgr.UserFlags.bv_term_abstraction_rounds = 1;
  mgr.UserFlags.bv_term_abstraction_schemas = false;

  NodeFactory* factory = mgr.defaultNodeFactory;
  const ASTNode a = mgr.CreateSymbol("budget_a", 0, WIDTH);
  const ASTNode b = mgr.CreateSymbol("budget_b", 0, WIDTH);
  const ASTNode product = factory->CreateTerm(BVMULT, WIDTH, a, b);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction record;
  record.termNode = product;
  record.opKind = BVMULT;
  record.operands[0] = a;
  record.operands[1] = b;
  record.numOperands = 2;
  record.width = WIDTH;
  appendTermRecord(refiner, record);

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  const std::vector<unsigned> aVars = makeVars(*solver);
  const std::vector<unsigned> bVars = makeVars(*solver);
  const std::vector<unsigned> resultVars = makeVars(*solver);

  ToSATBase::ASTNodeToSATVar nodeToVars;
  nodeToVars[a] = aVars;
  nodeToVars[b] = bVars;
  nodeToVars[product] = resultVars;

  // One operand pinned to 2 and the product pinned to the odd value 251. No
  // value of the free operand can make the abstraction
  // faithful, so every round has a candidate to reject and each blocking
  // lemma rules out one more of them. (Using 3 here would be wrong: 3 is
  // invertible modulo 2^32, so 3*b=251 does have a solution.)
  pin(*solver, aVars, 2);
  pin(*solver, resultVars, 251);

  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);

  // Round one: the allowance is untouched, so a blocking lemma.
  EXPECT_EQ(1u, refinedCount(refiner.refine(*solver, nodeToVars)));
  EXPECT_EQ(1u, refiner.terms()[0].blockedRounds);
  EXPECT_FALSE(refiner.terms()[0].exactRefused);
  EXPECT_EQ(0u, refiner.terms()[0].exactEscalations);

  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);

  // Round two: the allowance is spent, so the escalation is chosen and
  // refused. The result distinguishes that refusal from a faithful fixed
  // point without relying on the manager flag to interpret a count of zero.
  const AbstractionRefinementResult refused =
      refiner.refine(*solver, nodeToVars);
  EXPECT_TRUE(refused.isUnknown());
  EXPECT_EQ(0u, refused.refined);
  EXPECT_TRUE(refiner.terms()[0].exactRefused);
  EXPECT_GE(refiner.terms()[0].exactRefusedAtNodeCount, 0);
  EXPECT_EQ(0u, refiner.terms()[0].exactEscalations);
  EXPECT_FALSE(refiner.terms()[0].defined);
  EXPECT_EQ(1u, refiner.terms()[0].blockedRounds);
  EXPECT_TRUE(mgr.soft_timeout_expired);
}

// Every record that reports `defined` reports the width it was defined at.
//
// blastedBits is published by reportRecords as `exact-bits`, and its own
// comment says it is the width once `defined` is set. Three of the paths that
// set `defined` -- a comparison, an if-then-else and a whole addition -- left
// it at zero, so a fully defined record reported `exact-bits=0`; the two exact
// low-prefix schemas write it without any piece being blasted, so a record
// with no escalation at all reported `partial`. Both readings are the field
// doing what it says now.
//
// Driven through the refiner rather than by setting the field, because what is
// under test is that the paths write it, not that a struct can hold a number.
TEST_F(BVExactBudgetTest, EveryDefinedRecordReportsTheWidthItWasDefinedAt)
{
  mgr.UserFlags.aig_node_budget = -1;
  mgr.UserFlags.bv_term_abstraction_rounds = 1;
  mgr.UserFlags.bv_term_abstraction_schemas = false;

  NodeFactory* factory = mgr.defaultNodeFactory;
  const ASTNode a = mgr.CreateSymbol("defw_a", 0, WIDTH);
  const ASTNode b = mgr.CreateSymbol("defw_b", 0, WIDTH);
  const ASTNode compare = factory->CreateNode(BVLT, a, b);
  const ASTNode sum = factory->CreateTerm(BVPLUS, WIDTH, a, b);

  BVAbstractionRefiner refiner(&mgr);

  BVTermAbstraction compareRecord;
  compareRecord.termNode = compare;
  compareRecord.opKind = BVLT;
  compareRecord.operands[0] = a;
  compareRecord.operands[1] = b;
  compareRecord.numOperands = 2;
  compareRecord.width = WIDTH;

  BVTermAbstraction sumRecord;
  sumRecord.termNode = sum;
  sumRecord.opKind = BVPLUS;
  sumRecord.operands[0] = a;
  sumRecord.operands[1] = b;
  sumRecord.numOperands = 2;
  sumRecord.width = WIDTH;

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  const std::vector<unsigned> aVars = makeVars(*solver);
  const std::vector<unsigned> bVars = makeVars(*solver);
  const std::vector<unsigned> sumVars = makeVars(*solver);
  const unsigned condVar = solver->newVar();
  solver->setFrozen(condVar);
  compareRecord.condSATVar = condVar;
  appendTermRecord(refiner, compareRecord);
  appendTermRecord(refiner, sumRecord);

  ToSATBase::ASTNodeToSATVar nodeToVars;
  nodeToVars[a] = aVars;
  nodeToVars[b] = bVars;
  nodeToVars[sum] = sumVars;

  // a = 3 and b = 5, so the comparison is true and the sum is 8. The
  // abstraction is told neither: the condition and the sum bits are pinned to
  // the wrong answers, so both records are refined on the first round and
  // both are defined by it.
  pin(*solver, aVars, 3);
  pin(*solver, bVars, 5);
  pin(*solver, sumVars, 0);
  SATSolver::vec_literals unit;
  unit.push(SATSolver::mkLit(condVar, true));
  solver->addClause(unit);

  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);

  EXPECT_EQ(2u, refinedCount(refiner.refine(*solver, nodeToVars)));
  for (const BVTermAbstraction& record : refiner.terms())
  {
    EXPECT_TRUE(record.defined) << "kind=" << _kind_names[record.opKind];
    EXPECT_EQ(WIDTH, record.blastedBits)
        << "kind=" << _kind_names[record.opKind];
  }
}

// The same session with the budget lifted: the record escalates exactly as it
// always has. Without this the test above would pass just as well against a
// setup where the escalation is never reached at all, or where the operands
// are such that the second round finds nothing to refine.
TEST_F(BVExactBudgetTest, AnAffordableEscalationStillHappens)
{
  mgr.UserFlags.aig_node_budget = -1;
  mgr.UserFlags.bv_term_abstraction_rounds = 1;
  mgr.UserFlags.bv_term_abstraction_schemas = false;

  NodeFactory* factory = mgr.defaultNodeFactory;
  const ASTNode a = mgr.CreateSymbol("afford_a", 0, WIDTH);
  const ASTNode b = mgr.CreateSymbol("afford_b", 0, WIDTH);
  const ASTNode product = factory->CreateTerm(BVMULT, WIDTH, a, b);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction record;
  record.termNode = product;
  record.opKind = BVMULT;
  record.operands[0] = a;
  record.operands[1] = b;
  record.numOperands = 2;
  record.width = WIDTH;
  appendTermRecord(refiner, record);

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  const std::vector<unsigned> aVars = makeVars(*solver);
  const std::vector<unsigned> bVars = makeVars(*solver);
  const std::vector<unsigned> resultVars = makeVars(*solver);

  ToSATBase::ASTNodeToSATVar nodeToVars;
  nodeToVars[a] = aVars;
  nodeToVars[b] = bVars;
  nodeToVars[product] = resultVars;

  pin(*solver, aVars, 3);
  pin(*solver, resultVars, 251);

  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);
  EXPECT_EQ(1u, refinedCount(refiner.refine(*solver, nodeToVars)));

  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);
  EXPECT_EQ(1u, refinedCount(refiner.refine(*solver, nodeToVars)));

  EXPECT_FALSE(refiner.terms()[0].exactRefused);
  EXPECT_EQ(1u, refiner.terms()[0].exactEscalations);
  EXPECT_TRUE(refiner.terms()[0].defined);

  // With the mandatory circuit installed, the next model is a genuine fixed
  // point and is reported as Faithful rather than merely as count zero.
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);
  const AbstractionRefinementResult faithful =
      refiner.refine(*solver, nodeToVars);
  EXPECT_TRUE(faithful.isFaithful());
  EXPECT_EQ(0u, faithful.refined);
}

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

// A paired quotient and remainder can say what neither abstraction can say
// alone: x = q*s+r, taken mod 2^W. Check the value predicate, the clauses
// spliced onto live variables, and that the refiner reaches for the relation
// before either record spends a schema of its own.
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/BVExactEncoder.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <algorithm>
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

const unsigned WIDTH = 4;
const unsigned VALUES = 1u << WIDTH;

std::vector<bool> bitsOf(unsigned value, unsigned width = WIDTH)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

unsigned quotient(unsigned dividend, unsigned divisor, unsigned width)
{
  return divisor == 0 ? (1u << width) - 1 : dividend / divisor;
}

unsigned remainder(unsigned dividend, unsigned divisor)
{
  return divisor == 0 ? dividend : dividend % divisor;
}

bool referenceRelation(unsigned dividend, unsigned divisor,
                       unsigned quotientValue, unsigned remainderValue,
                       unsigned width = WIDTH)
{
  const unsigned mask = (1u << width) - 1;
  return (dividend & mask) ==
         ((quotientValue * divisor + remainderValue) & mask);
}

class BVDivRemSchemaTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  std::unique_ptr<SATSolver> makeSolver()
  {
    return std::unique_ptr<SATSolver>(createSATSolver(mgr.UserFlags));
  }

  std::vector<unsigned> makeVars(SATSolver& solver, unsigned width = WIDTH)
  {
    std::vector<unsigned> vars(width);
    for (unsigned i = 0; i < width; ++i)
    {
      vars[i] = solver.newVar();
      solver.setFrozen(vars[i]);
    }
    return vars;
  }

  ASTNode productNode(unsigned width = WIDTH)
  {
    const ASTNode quotient = mgr.CreateSymbol("dr_q", 0, width);
    const ASTNode divisor = mgr.CreateSymbol("dr_s", 0, width);
    return mgr.defaultNodeFactory->CreateTerm(BVMULT, width, quotient,
                                               divisor);
  }

  void pin(SATSolver& solver, const std::vector<unsigned>& vars,
           unsigned value)
  {
    SATSolver::vec_literals unit;
    for (unsigned i = 0; i < vars.size(); ++i)
    {
      unit.clear();
      unit.push(SATSolver::mkLit(vars[i], ((value >> i) & 1u) == 0));
      solver.addClause(unit);
    }
  }
};

} // namespace

TEST(BVDivRemSchema, actual_results_satisfy_recomposition_at_small_widths)
{
  for (unsigned width = 1; width <= 6; ++width)
  {
    const unsigned values = 1u << width;
    for (unsigned dividend = 0; dividend < values; ++dividend)
      for (unsigned divisor = 0; divisor < values; ++divisor)
        ASSERT_TRUE(divRemIdentityHolds(
            bitsOf(dividend, width), bitsOf(divisor, width),
            bitsOf(quotient(dividend, divisor, width), width),
            bitsOf(remainder(dividend, divisor), width)))
            << "width=" << width << " dividend=" << dividend
            << " divisor=" << divisor;
  }
}

TEST(BVDivRemSchema, value_predicate_matches_modular_recomposition)
{
  for (unsigned dividend = 0; dividend < VALUES; ++dividend)
    for (unsigned divisor = 0; divisor < VALUES; ++divisor)
      for (unsigned q = 0; q < VALUES; ++q)
        for (unsigned r = 0; r < VALUES; ++r)
          ASSERT_EQ(referenceRelation(dividend, divisor, q, r),
                    divRemIdentityHolds(bitsOf(dividend), bitsOf(divisor),
                                        bitsOf(q), bitsOf(r)))
              << "dividend=" << dividend << " divisor=" << divisor
              << " q=" << q << " r=" << r;
}

TEST_F(BVDivRemSchemaTest, clauses_match_modular_recomposition)
{
  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  ASSERT_TRUE(solver->supportsAssumptions());

  const std::vector<unsigned> dividendVars = makeVars(*solver);
  const std::vector<unsigned> divisorVars = makeVars(*solver);
  const std::vector<unsigned> quotientVars = makeVars(*solver);
  const std::vector<unsigned> remainderVars = makeVars(*solver);
  BVExactEncoder(&mgr).encodeDivRemIdentity(
      *solver, productNode(), WIDTH, dividendVars, divisorVars, quotientVars,
      remainderVars);

  const std::vector<unsigned>* vars[4] = {
      &dividendVars, &divisorVars, &quotientVars, &remainderVars};
  for (unsigned dividend = 0; dividend < VALUES; ++dividend)
    for (unsigned divisor = 0; divisor < VALUES; ++divisor)
      for (unsigned q = 0; q < VALUES; ++q)
        for (unsigned r = 0; r < VALUES; ++r)
        {
          const unsigned values[4] = {dividend, divisor, q, r};
          SATSolver::vec_literals assumptions;
          for (unsigned v = 0; v < 4; ++v)
            for (unsigned i = 0; i < WIDTH; ++i)
              assumptions.push(SATSolver::mkLit(
                  (*vars[v])[i], ((values[v] >> i) & 1u) == 0));

          bool timedOut = false;
          const bool satisfiable =
              solver->solveWithAssumptions(assumptions, timedOut);
          ASSERT_FALSE(timedOut);
          ASSERT_EQ(referenceRelation(dividend, divisor, q, r, WIDTH),
                    satisfiable)
              << "dividend=" << dividend << " divisor=" << divisor
              << " q=" << q << " r=" << r;
        }
}

TEST_F(BVDivRemSchemaTest, refiner_pairs_identical_division_operands)
{
  // The paired identity builds a full-width multiplier, so it sits outside
  // every inherited profile and has to be asked for on its own.
  mgr.UserFlags.bv_term_abstraction_schema_groups =
      bvSchemaGroupBit(BVSchemaGroup::DIVREM_FULL);
  NodeFactory* factory = mgr.defaultNodeFactory;
  const ASTNode dividend = mgr.CreateSymbol("dr_dividend", 0, WIDTH);
  const ASTNode divisor = mgr.CreateSymbol("dr_divisor", 0, WIDTH);
  const ASTNode div = factory->CreateTerm(BVDIV, WIDTH, dividend, divisor);
  const ASTNode rem = factory->CreateTerm(BVMOD, WIDTH, dividend, divisor);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction divRecord;
  divRecord.termNode = div;
  divRecord.opKind = BVDIV;
  divRecord.operands[0] = dividend;
  divRecord.operands[1] = divisor;
  divRecord.numOperands = 2;
  divRecord.width = WIDTH;
  appendTermRecord(refiner, divRecord);

  BVTermAbstraction remRecord;
  remRecord.termNode = rem;
  remRecord.opKind = BVMOD;
  remRecord.operands[0] = dividend;
  remRecord.operands[1] = divisor;
  remRecord.numOperands = 2;
  remRecord.width = WIDTH;
  appendTermRecord(refiner, remRecord);

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  const std::vector<unsigned> dividendVars = makeVars(*solver);
  const std::vector<unsigned> divisorVars = makeVars(*solver);
  const std::vector<unsigned> quotientVars = makeVars(*solver);
  const std::vector<unsigned> remainderVars = makeVars(*solver);

  ToSATBase::ASTNodeToSATVar nodeToVars;
  nodeToVars[dividend] = dividendVars;
  nodeToVars[divisor] = divisorVars;
  nodeToVars[div] = quotientVars;
  nodeToVars[rem] = remainderVars;

  // x=13, s=3, but q=r=0: recomposition says 13=0, so the paired lemma
  // must reject this candidate before either record spends an individual
  // schema or blocking lemma.
  pin(*solver, dividendVars, 13);
  pin(*solver, divisorVars, 3);
  pin(*solver, quotientVars, 0);
  pin(*solver, remainderVars, 0);
  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);

  EXPECT_EQ(1u, refinedCount(refiner.refine(*solver, nodeToVars)));
  EXPECT_TRUE(refiner.terms()[0].divRemFullInstalled);
  EXPECT_TRUE(refiner.terms()[1].divRemFullInstalled);
  EXPECT_EQ(1u, refiner.terms()[0].schemaRounds);
  EXPECT_EQ(1u, refiner.terms()[1].schemaRounds);
  EXPECT_EQ(0u, refiner.terms()[0].blockedRounds);
  EXPECT_EQ(0u, refiner.terms()[1].blockedRounds);
  EXPECT_EQ(1u, mgr.UserFlags.coverage.bv_schema_lemmas);
  EXPECT_EQ(1u,
            mgr.UserFlags.coverage.bv_schema_group_lemmas[static_cast<unsigned>(
                BVSchemaGroup::DIVREM_FULL)]);
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    if (i == static_cast<unsigned>(BVSchemaGroup::DIVREM_FULL))
      continue;
    EXPECT_EQ(0u, mgr.UserFlags.coverage.bv_schema_group_lemmas[i]);
  }

  EXPECT_FALSE(solver->solve(timedOut));
  EXPECT_FALSE(timedOut);
}

// The shared identity is an optional schema. Its multiplier may be much more
// expensive than either record's ordinary value lemma, so refusing it must
// disable only the schema and refine the cached DIV/MOD inconsistencies in
// the same round. In particular, it is not the mandatory exact backstop and
// must not turn the whole query into Unknown.
TEST_F(BVDivRemSchemaTest,
       refused_paired_identity_falls_through_to_individual_refinement)
{
  mgr.UserFlags.aig_node_budget = 1;
  mgr.UserFlags.bv_term_abstraction_schema_groups =
      bvSchemaGroupBit(BVSchemaGroup::DIVREM_FULL);

  NodeFactory* factory = mgr.defaultNodeFactory;
  const ASTNode dividend = mgr.CreateSymbol("refused_dividend", 0, WIDTH);
  const ASTNode divisor = mgr.CreateSymbol("refused_divisor", 0, WIDTH);
  const ASTNode div = factory->CreateTerm(BVDIV, WIDTH, dividend, divisor);
  const ASTNode rem = factory->CreateTerm(BVMOD, WIDTH, dividend, divisor);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction divRecord;
  divRecord.termNode = div;
  divRecord.opKind = BVDIV;
  divRecord.operands[0] = dividend;
  divRecord.operands[1] = divisor;
  divRecord.numOperands = 2;
  divRecord.width = WIDTH;
  appendTermRecord(refiner, divRecord);

  BVTermAbstraction remRecord;
  remRecord.termNode = rem;
  remRecord.opKind = BVMOD;
  remRecord.operands[0] = dividend;
  remRecord.operands[1] = divisor;
  remRecord.numOperands = 2;
  remRecord.width = WIDTH;
  appendTermRecord(refiner, remRecord);

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  const std::vector<unsigned> dividendVars = makeVars(*solver);
  const std::vector<unsigned> divisorVars = makeVars(*solver);
  const std::vector<unsigned> quotientVars = makeVars(*solver);
  const std::vector<unsigned> remainderVars = makeVars(*solver);

  ToSATBase::ASTNodeToSATVar nodeToVars;
  nodeToVars[dividend] = dividendVars;
  nodeToVars[divisor] = divisorVars;
  nodeToVars[div] = quotientVars;
  nodeToVars[rem] = remainderVars;

  // x=13,s=3 has q=4,r=1. Pinning both abstract results to zero makes the
  // pair and both individual records inconsistent.
  pin(*solver, dividendVars, 13);
  pin(*solver, divisorVars, 3);
  pin(*solver, quotientVars, 0);
  pin(*solver, remainderVars, 0);
  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);

  const AbstractionRefinementResult result =
      refiner.refine(*solver, nodeToVars);
  EXPECT_TRUE(result.madeProgress());
  EXPECT_EQ(2u, result.refined);
  for (const BVTermAbstraction& record : refiner.terms())
  {
    EXPECT_TRUE(record.divRemFullRefused);
    EXPECT_FALSE(record.divRemFullInstalled);
    EXPECT_EQ(1u, record.blockedRounds);
  }
  EXPECT_EQ(0u, mgr.UserFlags.coverage.bv_schema_lemmas);
  EXPECT_FALSE(mgr.soft_timeout_expired);

  EXPECT_FALSE(solver->solve(timedOut));
  EXPECT_FALSE(timedOut);
}

// Incremental lowering can retain more than one abstraction record for a
// hash-consed term. The AST-keyed map then names whichever result was
// registered last, while each durable record owns the result variables its
// candidate actually uses. A paired lemma must inspect and constrain those
// record-owned variables on both sides, just like every single-record path.
TEST_F(BVDivRemSchemaTest, paired_lemma_uses_each_records_owned_result)
{
  mgr.UserFlags.bv_term_abstraction_schema_groups =
      bvSchemaGroupBit(BVSchemaGroup::DIVREM_FULL);
  NodeFactory* factory = mgr.defaultNodeFactory;
  const ASTNode dividend = mgr.CreateSymbol("owned_dividend", 0, WIDTH);
  const ASTNode divisor = mgr.CreateSymbol("owned_divisor", 0, WIDTH);
  const ASTNode div = factory->CreateTerm(BVDIV, WIDTH, dividend, divisor);
  const ASTNode rem = factory->CreateTerm(BVMOD, WIDTH, dividend, divisor);

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  const std::vector<unsigned> dividendVars = makeVars(*solver);
  const std::vector<unsigned> divisorVars = makeVars(*solver);
  const std::vector<unsigned> ownedQuotientVars = makeVars(*solver);
  const std::vector<unsigned> ownedRemainderVars = makeVars(*solver);
  const std::vector<unsigned> mappedQuotientVars = makeVars(*solver);
  const std::vector<unsigned> mappedRemainderVars = makeVars(*solver);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction divRecord;
  divRecord.termNode = div;
  divRecord.opKind = BVDIV;
  divRecord.operands[0] = dividend;
  divRecord.operands[1] = divisor;
  divRecord.numOperands = 2;
  divRecord.width = WIDTH;
  divRecord.resultSATVars = ownedQuotientVars;
  appendTermRecord(refiner, divRecord);

  BVTermAbstraction remRecord;
  remRecord.termNode = rem;
  remRecord.opKind = BVMOD;
  remRecord.operands[0] = dividend;
  remRecord.operands[1] = divisor;
  remRecord.numOperands = 2;
  remRecord.width = WIDTH;
  remRecord.resultSATVars = ownedRemainderVars;
  appendTermRecord(refiner, remRecord);

  ToSATBase::ASTNodeToSATVar nodeToVars;
  nodeToVars[dividend] = dividendVars;
  nodeToVars[divisor] = divisorVars;
  nodeToVars[div] = mappedQuotientVars;
  nodeToVars[rem] = mappedRemainderVars;

  // x=13 and s=3. The map's q=4,r=1 satisfies recomposition, while the
  // durable records' q=r=0 do not. Reading the map would miss the paired
  // violation; writing the lemma to the map would fail to block it.
  pin(*solver, dividendVars, 13);
  pin(*solver, divisorVars, 3);
  pin(*solver, ownedQuotientVars, 0);
  pin(*solver, ownedRemainderVars, 0);
  pin(*solver, mappedQuotientVars, 4);
  pin(*solver, mappedRemainderVars, 1);
  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);

  EXPECT_EQ(1u, refinedCount(refiner.refine(*solver, nodeToVars)));
  EXPECT_TRUE(refiner.terms()[0].divRemFullInstalled);
  EXPECT_TRUE(refiner.terms()[1].divRemFullInstalled);
  EXPECT_EQ(1u, mgr.UserFlags.coverage.bv_schema_lemmas);

  EXPECT_FALSE(solver->solve(timedOut));
  EXPECT_FALSE(timedOut);
}

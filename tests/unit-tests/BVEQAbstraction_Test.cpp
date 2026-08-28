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

#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_MaxPrecision.h"
#include "stp/STPManager/STP.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/ToSATAIG.h"

#include <gtest/gtest.h>

#include <map>
#include <set>
#include <utility>
#include <vector>

using namespace stp;

namespace
{

void appendEqualityRecord(BVAbstractionRefiner& refiner,
                          BVEQAbstraction record)
{
  static uint64_t nextId = 1;
  record.id = BVAbstractionId(nextId++);
  refiner.appendEquality(record);
}

void appendTermRecord(BVAbstractionRefiner& refiner,
                      BVTermAbstraction record)
{
  static uint64_t nextId = UINT64_C(1) << 32;
  record.id = BVAbstractionId(nextId++);
  refiner.appendTerm(record);
}


class BVEQAbstractionTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  NodeFactory* factory;

  void SetUp() override { factory = mgr.defaultNodeFactory; }

  ASTNode makeSymbol(const char* name, unsigned width)
  {
    return mgr.CreateSymbol(name, 0, width);
  }
};

TEST_F(BVEQAbstractionTest, AbstractsWideSymbolEquality)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode x = makeSymbol("x", 256);
  ASTNode y = makeSymbol("y", 256);
  ASTNode eq = factory->CreateNode(EQ, x, y);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_EQ(1u, bb.abstractedEQs().size());
  EXPECT_EQ(eq, bb.abstractedEQs()[0].eqNode);
  EXPECT_EQ(x, bb.abstractedEQs()[0].leftSymbol);
  EXPECT_EQ(y, bb.abstractedEQs()[0].rightSymbol);
}

TEST_F(BVEQAbstractionTest, NoAbstractionWhenDisabled)
{
  mgr.UserFlags.bv_eq_abstraction = false;

  ASTNode x = makeSymbol("x2", 256);
  ASTNode y = makeSymbol("y2", 256);
  ASTNode eq = factory->CreateNode(EQ, x, y);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_TRUE(bb.abstractedEQs().empty());
}

TEST_F(BVEQAbstractionTest, NoAbstractionBelowWidthThreshold)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode x = makeSymbol("x3", 32);
  ASTNode y = makeSymbol("y3", 32);
  ASTNode eq = factory->CreateNode(EQ, x, y);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_TRUE(bb.abstractedEQs().empty());
}

TEST_F(BVEQAbstractionTest, AbstractionWithNonSymbolOperandsViaProxyCIs)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode x = makeSymbol("x4", 256);
  ASTNode one = mgr.CreateBVConst(256, 1);
  ASTNode sum = factory->CreateTerm(BVPLUS, 256, x, one);
  ASTNode y = makeSymbol("y4", 256);
  ASTNode eq = factory->CreateNode(EQ, sum, y);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_EQ(1u, bb.abstractedEQs().size());
  EXPECT_FALSE(bb.sideConstraints().empty());
}

TEST_F(BVEQAbstractionTest, BooleanSkeletonContradictionIsUnsatWithoutRefinement)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode x = makeSymbol("x5", 256);
  ASTNode y = makeSymbol("y5", 256);
  ASTNode eq = factory->CreateNode(EQ, x, y);
  ASTNode neq = factory->CreateNode(NOT, eq);
  ASTNode conj = factory->CreateNode(AND, eq, neq);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  BBNodeAIG result = bb.BBForm(conj);

  EXPECT_EQ(1u, bb.abstractedEQs().size());
  EXPECT_EQ(aigMgr.getFalse(), result);
}

TEST_F(BVEQAbstractionTest, MultipleEqualitiesAbstracted)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode a = makeSymbol("a", 256);
  ASTNode b = makeSymbol("b", 256);
  ASTNode c = makeSymbol("c", 256);
  ASTNode eq1 = factory->CreateNode(EQ, a, b);
  ASTNode eq2 = factory->CreateNode(EQ, b, c);
  ASTNode conj = factory->CreateNode(AND, eq1, eq2);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(conj);

  EXPECT_EQ(2u, bb.abstractedEQs().size());
}

TEST_F(BVEQAbstractionTest, DagSharingReusesAbstraction)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode x = makeSymbol("x6", 256);
  ASTNode y = makeSymbol("y6", 256);
  ASTNode eq = factory->CreateNode(EQ, x, y);
  ASTNode conj = factory->CreateNode(AND, eq, eq);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(conj);

  EXPECT_EQ(1u, bb.abstractedEQs().size());
}

TEST_F(BVEQAbstractionTest, PrefixRefinementSatResult)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;
  mgr.UserFlags.bv_eq_refine_width = 32;

  ASTNode a = makeSymbol("pr_a", 256);
  ASTNode b = makeSymbol("pr_b", 256);
  ASTNode eq = factory->CreateNode(EQ, a, b);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(eq, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQAbstractionTest, PrefixRefinementUnsatTransitivity)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;
  mgr.UserFlags.bv_eq_refine_width = 32;

  ASTNode a = makeSymbol("pru_a", 256);
  ASTNode b = makeSymbol("pru_b", 256);
  ASTNode c = makeSymbol("pru_c", 256);

  ASTNode eq_ab = factory->CreateNode(EQ, a, b);
  ASTNode eq_bc = factory->CreateNode(EQ, b, c);
  ASTNode neq_ac = factory->CreateNode(NOT, factory->CreateNode(EQ, a, c));

  ASTNode formula = factory->CreateNode(AND, eq_ab,
      factory->CreateNode(AND, eq_bc, neq_ac));

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

TEST_F(BVEQAbstractionTest, PrefixRefinementSmallWidth)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;
  mgr.UserFlags.bv_eq_refine_width = 8;

  ASTNode a = makeSymbol("psm_a", 256);
  ASTNode b = makeSymbol("psm_b", 256);

  ASTNode eq = factory->CreateNode(EQ, a, b);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(eq, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQAbstractionTest, BVPLUSAbstractionCreatesAbstraction)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode x = makeSymbol("ta_x", 256);
  ASTNode y = makeSymbol("ta_y", 256);
  ASTNode sum = factory->CreateTerm(BVPLUS, 256, x, y);
  ASTNode z = makeSymbol("ta_z", 256);
  ASTNode eq = factory->CreateNode(EQ, sum, z);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_GE(bb.abstractedTerms().size(), 1u);
  EXPECT_EQ(BVPLUS, bb.abstractedTerms()[0].opKind);
}

TEST_F(BVEQAbstractionTest, BVPLUSAbstractionSatResult)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode x = makeSymbol("tas_x", 256);
  ASTNode y = makeSymbol("tas_y", 256);
  ASTNode sum = factory->CreateTerm(BVPLUS, 256, x, y);
  ASTNode z = makeSymbol("tas_z", 256);
  ASTNode eq = factory->CreateNode(EQ, sum, z);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(eq, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQAbstractionTest, BVPLUSAbstractionUnsatResult)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode x = makeSymbol("tau_x", 256);
  ASTNode y = makeSymbol("tau_y", 256);
  ASTNode z = makeSymbol("tau_z", 256);
  ASTNode sum = factory->CreateTerm(BVPLUS, 256, x, y);
  ASTNode eqSumZ = factory->CreateNode(EQ, sum, z);
  ASTNode eqXZ = factory->CreateNode(EQ, x, z);
  ASTNode yNeq0 = factory->CreateNode(NOT,
      factory->CreateNode(EQ, y, mgr.CreateBVConst(256, 0)));
  ASTNode formula = factory->CreateNode(AND,
      factory->CreateNode(AND, eqSumZ, eqXZ), yNeq0);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

TEST_F(BVEQAbstractionTest, BVPLUSSubtractionAbstraction)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  // x - y = z (encoded as x + (-y) = z) is SAT
  ASTNode x = makeSymbol("sub_x", 256);
  ASTNode y = makeSymbol("sub_y", 256);
  ASTNode z = makeSymbol("sub_z", 256);
  ASTNode negY = factory->CreateTerm(BVUMINUS, 256, y);
  ASTNode diff = factory->CreateTerm(BVPLUS, 256, x, negY);
  ASTNode eq = factory->CreateNode(EQ, diff, z);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(eq, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQAbstractionTest, BVPLUSSubtractionUnsatResult)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  // x - y = z AND x = z AND y != 0 → UNSAT (forces y = 0 but y ≠ 0)
  ASTNode x = makeSymbol("subu_x", 256);
  ASTNode y = makeSymbol("subu_y", 256);
  ASTNode z = makeSymbol("subu_z", 256);
  ASTNode negY = factory->CreateTerm(BVUMINUS, 256, y);
  ASTNode diff = factory->CreateTerm(BVPLUS, 256, x, negY);
  ASTNode eqDiffZ = factory->CreateNode(EQ, diff, z);
  ASTNode eqXZ = factory->CreateNode(EQ, x, z);
  ASTNode yNeq0 = factory->CreateNode(NOT,
      factory->CreateNode(EQ, y, mgr.CreateBVConst(256, 0)));
  ASTNode formula = factory->CreateNode(AND,
      factory->CreateNode(AND, eqDiffZ, eqXZ), yNeq0);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

TEST_F(BVEQAbstractionTest, BVPLUSConstantOperandAbstraction)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  // x + 1 = y is SAT
  ASTNode x = makeSymbol("ca_x", 256);
  ASTNode y = makeSymbol("ca_y", 256);
  ASTNode one = mgr.CreateBVConst(256, 1);
  ASTNode sum = factory->CreateTerm(BVPLUS, 256, x, one);
  ASTNode eq = factory->CreateNode(EQ, sum, y);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(eq, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQAbstractionTest, ITEAbstractionCreatesAbstraction)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode p = makeSymbol("ite_p", 0);
  ASTNode x = makeSymbol("ite_x", 256);
  ASTNode y = makeSymbol("ite_y", 256);
  ASTNode ite = factory->CreateTerm(ITE, 256, p, x, y);
  ASTNode z = makeSymbol("ite_z", 256);
  ASTNode eq = factory->CreateNode(EQ, ite, z);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  bool foundITE = false;
  for (const auto& a : bb.abstractedTerms())
    if (a.opKind == ITE) foundITE = true;
  EXPECT_TRUE(foundITE);
  EXPECT_FALSE(bb.sideConstraints().empty());
}

TEST_F(BVEQAbstractionTest, ITEAbstractionSatResult)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  // ite(p, x, y) = z is trivially SAT
  ASTNode p = makeSymbol("ites_p", 0);
  ASTNode x = makeSymbol("ites_x", 256);
  ASTNode y = makeSymbol("ites_y", 256);
  ASTNode z = makeSymbol("ites_z", 256);
  ASTNode ite = factory->CreateTerm(ITE, 256, p, x, y);
  ASTNode eq = factory->CreateNode(EQ, ite, z);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(eq, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQAbstractionTest, ITEAbstractionUnsatResult)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  // ite(p, x, y) = z AND x != z AND y != z → UNSAT
  ASTNode p = makeSymbol("iteu_p", 0);
  ASTNode x = makeSymbol("iteu_x", 256);
  ASTNode y = makeSymbol("iteu_y", 256);
  ASTNode z = makeSymbol("iteu_z", 256);
  ASTNode ite = factory->CreateTerm(ITE, 256, p, x, y);
  ASTNode eqIteZ = factory->CreateNode(EQ, ite, z);
  ASTNode xNeqZ = factory->CreateNode(NOT, factory->CreateNode(EQ, x, z));
  ASTNode yNeqZ = factory->CreateNode(NOT, factory->CreateNode(EQ, y, z));
  ASTNode formula = factory->CreateNode(AND,
      factory->CreateNode(AND, eqIteZ, xNeqZ), yNeqZ);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

// Incremental pieces do not necessarily share the ordinary BBTerm memo. The
// long-lived node registry is the canonical name of a term across that
// boundary: revisiting an abstractable operation must return the first result
// vector without filing another record. Per-record result ownership remains a
// backstop, but the normal path should not pay for duplicate abstractions.
TEST_F(BVEQAbstractionTest, ReusesTermAbstractionsAcrossMemoBoundaries)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_term_abstraction_ite = true;
  mgr.UserFlags.bv_term_abstraction_plus = true;
  mgr.UserFlags.bv_term_abstraction_mult = true;
  mgr.UserFlags.bv_term_abstraction_compare = false;
  mgr.UserFlags.bv_eq_abstraction = false;
  mgr.UserFlags.bv_abstraction_width = 1;
  mgr.UserFlags.fp_native_domain = true;

  ASTNode condition = makeSymbol("reuse_abs_condition", 0);
  ASTNode left = makeSymbol("reuse_abs_left", 8);
  ASTNode right = makeSymbol("reuse_abs_right", 8);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  const auto expectReused = [&](const ASTNode& term, Kind expectedKind)
  {
    const size_t recordsBefore = bb.abstractedTerms().size();
    const ASTNode firstRoot = factory->CreateNode(EQ, term, left);
    const ASTNode secondRoot = factory->CreateNode(EQ, term, right);

    bb.BBForm(firstRoot);

    ASSERT_EQ(recordsBefore + 1, bb.abstractedTerms().size());
    EXPECT_EQ(expectedKind, bb.abstractedTerms().back().opKind);
    EXPECT_EQ(term.GetValueWidth(),
              bb.abstractedTerms().back().resultCISymbolIndices.size());
    const auto firstRegistration = aigMgr.symbolToBBNode.find(term);
    ASSERT_TRUE(firstRegistration != aigMgr.symbolToBBNode.end());
    const BBNodeVec first = firstRegistration->second;

    // A different FP-domain root clears BBTermMemo before this visit, as the
    // incremental per-piece route does for distinct conjuncts.
    bb.BBForm(secondRoot);

    const auto secondRegistration = aigMgr.symbolToBBNode.find(term);
    ASSERT_TRUE(secondRegistration != aigMgr.symbolToBBNode.end());
    EXPECT_EQ(first, secondRegistration->second);
    EXPECT_EQ(recordsBefore + 1, bb.abstractedTerms().size());
  };

  expectReused(factory->CreateTerm(ITE, 8, condition, left, right), ITE);
  expectReused(factory->CreateTerm(BVPLUS, 8, left, right), BVPLUS);
  expectReused(factory->CreateTerm(BVMULT, 8, left, right), BVMULT);
  expectReused(factory->CreateTerm(BVDIV, 8, left, right), BVDIV);
}

// A candidate is only an assignment of the query once every abstraction in it
// has been checked against the operands it stands for. Refinement checks them
// by reading the operands' bits out of one map from node to SAT variables, and
// the four tests below hand it a map that cannot answer: an operand missing
// altogether, an operand with fewer bits than the record claims, an operand
// with a bit that never reached the CNF, and a comparison with no input of its
// own. None of the four can arise -- the blaster registers everything it
// abstracts, the widths are the same node's, and both lowerings carry the
// whole registry across -- but each used to be treated as though the
// abstraction had been checked and found consistent, which for an
// over-approximation means certified: a record nothing can contradict lets the
// search satisfy the query by giving the abstraction whatever value suits it,
// and an unsatisfiable query comes back sat.
//
// Reading the bits regardless is no better: past the end of the vector is an
// out-of-bounds read, and ~0u is a variable the backend does not have.
class NoModelSolver : public SATSolver
{
public:
  bool okay() const override { return true; }
  // Every abstraction reads as false, which is a candidate like any other.
  uint8_t modelValue(uint32_t) const override { return false_literal(); }
  uint32_t newVar() override { return next++; }
  uint32_t nVars() const override { return next; }
  void printStats() const override {}
  void setVerbosity(int) override {}
  lbool true_literal() const override { return 0; }
  lbool false_literal() const override { return 1; }
  lbool undef_literal() const override { return 2; }

protected:
  bool addClauseInternal(const vec_literals&) override { return true; }
  bool solveInternal(bool&) override { return true; }

private:
  uint32_t next = 1;
};

// A backend that records what STP does to it: the model is scripted per
// variable (anything unscripted reads false), every added clause is kept
// decoded, and setFrozen calls land in a set. Variables number from zero so
// ToSATAIG::CallSAT's fresh-solver assertion holds and add_cnf_to_solver can
// allocate the CNF's variables here.
class RecordingSolver : public SATSolver
{
public:
  std::map<uint32_t, bool> model;
  // Each clause as (variable, negated) pairs, in push order.
  std::vector<std::vector<std::pair<uint32_t, bool>>> clauses;
  std::set<uint32_t> frozen;
  uint32_t newVarCalls = 0;

  bool okay() const override { return true; }
  uint8_t modelValue(uint32_t v) const override
  {
    auto it = model.find(v);
    return (it != model.end() && it->second) ? true_literal()
                                             : false_literal();
  }
  uint32_t newVar() override
  {
    newVarCalls++;
    return next++;
  }
  uint32_t nVars() const override { return next; }
  void printStats() const override {}
  void setVerbosity(int) override {}
  void setFrozen(uint32_t v) override { frozen.insert(v); }
  lbool true_literal() const override { return 0; }
  lbool false_literal() const override { return 1; }
  lbool undef_literal() const override { return 2; }

  // TRUE when the scripted model falsifies every literal of some recorded
  // clause -- that clause rules the model out. Only clauses written
  // entirely over scripted variables count: a clause naming a variable the
  // model does not script (a fresh Tseitin helper, say) constrains the
  // helper, not the candidate. A literal (var, negated) is false exactly
  // when the scripted value equals its negation flag.
  bool someClauseBlocksModel() const
  {
    for (const auto& clause : clauses)
    {
      bool blocked = !clause.empty();
      for (const auto& lit : clause)
      {
        auto it = model.find(lit.first);
        if (it == model.end() || it->second != lit.second)
        {
          blocked = false;
          break;
        }
      }
      if (blocked)
        return true;
    }
    return false;
  }

protected:
  bool addClauseInternal(const vec_literals& ps) override
  {
    std::vector<std::pair<uint32_t, bool>> clause;
    for (int i = 0; i < ps.size(); i++)
      clause.push_back({SATSolver::var(ps[i]), SATSolver::sign(ps[i])});
    clauses.push_back(clause);
    return true;
  }
  bool solveInternal(bool&) override { return true; }

private:
  uint32_t next = 0;
};

// Refinement writes clauses over the records' own variables and the
// operands' bits in later solve calls, so every one of them has to be
// frozen before a simplifying backend's first solve can eliminate it. A
// ~0u entry is the pre-solve "not there yet" state and must be skipped,
// not handed to the backend as a variable index.
TEST_F(BVEQAbstractionTest, FreezeVariablesCoversEveryLemmaVariable)
{
  ASTNode x = makeSymbol("fz_x", 4);
  ASTNode y = makeSymbol("fz_y", 4);
  ASTNode sum = factory->CreateTerm(BVPLUS, 4, x, y);

  BVAbstractionRefiner refiner(&mgr);

  BVEQAbstraction eq;
  eq.eqNode = factory->CreateNode(EQ, x, y);
  eq.abstractionSATVar = 5;
  eq.leftSymbol = x;
  eq.rightSymbol = y;
  eq.width = 4;
  appendEqualityRecord(refiner, eq);

  // Harvested with no variable yet: legal before the first solve, skipped.
  BVEQAbstraction pending = eq;
  pending.abstractionSATVar = BV_ABSTRACTION_NO_VAR;
  appendEqualityRecord(refiner, pending);

  BVTermAbstraction term;
  term.termNode = sum;
  term.opKind = BVPLUS;
  term.operands[0] = x;
  term.operands[1] = y;
  term.numOperands = 2;
  term.width = 4;
  appendTermRecord(refiner, term);

  // A record that owns its result, as the persistent incremental lowering
  // files them. Freezing has to reach 40..43 and not whatever the node map
  // says for the same term, or the backend is free to eliminate the very
  // variables refinement will write its lemmas over. The record above owns
  // nothing and keeps the map fallback covered.
  BVTermAbstraction owned = term;
  owned.resultSATVars = std::vector<unsigned>{40, 41, 42, 43};
  appendTermRecord(refiner, owned);

  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>{10, 11, 12, 13};
  bits[y] = std::vector<unsigned>{20, 21, BV_ABSTRACTION_NO_VAR, 23};
  bits[sum] = std::vector<unsigned>{30, 31, 32, 33};

  RecordingSolver solver;
  refiner.freezeVariables(solver, bits);

  const std::set<uint32_t> expected = {5,  10, 11, 12, 13, 20, 21, 23,
                                       30, 31, 32, 33, 40, 41, 42, 43};
  EXPECT_EQ(expected, solver.frozen);
}

// Canonical bit-blaster reuse normally prevents more than one abstraction
// record for the same rewritten term. The refiner must not rely on that
// producer-side invariant, though: the AST-keyed registry names only the
// newest result, so every record must retain and refine its own free inputs.
TEST_F(BVEQAbstractionTest, DuplicateTermsKeepTheirOwnResultVariables)
{
  mgr.UserFlags.bv_term_abstraction_schemas = false;

  ASTNode a = makeSymbol("duplicate_result_a", 4);
  ASTNode b = makeSymbol("duplicate_result_b", 4);
  ASTNode product = factory->CreateTerm(BVMULT, 4, a, b);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction older;
  older.termNode = product;
  older.opKind = BVMULT;
  older.operands[0] = a;
  older.operands[1] = b;
  older.numOperands = 2;
  older.width = 4;
  older.resultSATVars = std::vector<unsigned>{40, 41, 42, 43};
  appendTermRecord(refiner, older);

  BVTermAbstraction newer = older;
  newer.resultSATVars = std::vector<unsigned>{30, 31, 32, 33};
  appendTermRecord(refiner, newer);

  ToSATBase::ASTNodeToSATVar bits;
  bits[a] = std::vector<unsigned>{10, 11, 12, 13};
  bits[b] = std::vector<unsigned>{20, 21, 22, 23};
  // The historical map has necessarily been overwritten by the newer
  // record. It cannot identify the result still used by the older root.
  bits[product] = newer.resultSATVars;

  RecordingSolver solver;
  // Both operands are 3, so their four-bit product is 9. The newer result is
  // correct while the older result says zero. Looking up both records by AST
  // would call the whole candidate consistent; record-owned variables expose
  // and block the older inconsistency.
  const bool operand[4] = {true, true, false, false};
  const bool expected[4] = {true, false, false, true};
  for (unsigned i = 0; i < 4; ++i)
  {
    solver.model[10 + i] = operand[i];
    solver.model[20 + i] = operand[i];
    solver.model[30 + i] = expected[i];
    solver.model[40 + i] = false;
  }

  EXPECT_EQ(1u, refiner.refine(solver, bits));
  EXPECT_EQ(1u, refiner.terms()[0].blockedRounds);
  EXPECT_EQ(0u, refiner.terms()[1].blockedRounds);
  EXPECT_TRUE(solver.someClauseBlocksModel());
}

// A partial prefix says nothing to a candidate that called the equality
// false over agreeing bits: every prefix clause is conditioned on the
// Boolean being true, so the identical candidate could come back round
// after round until the definition completed, one full solve per doubling
// of the prefix. Such a round must also emit a clause the candidate
// violates -- the definition's consequence at the candidate's own value:
// if both sides hold that value, the equality is true.
TEST_F(BVEQAbstractionTest, SaidUnequalRoundBlocksTheCandidate)
{
  mgr.UserFlags.bv_eq_refine_width = 1;

  ASTNode x = makeSymbol("cb_x", 4);
  ASTNode y = makeSymbol("cb_y", 4);

  BVAbstractionRefiner refiner(&mgr);
  BVEQAbstraction record;
  record.eqNode = factory->CreateNode(EQ, x, y);
  record.abstractionSATVar = 5;
  record.leftSymbol = x;
  record.rightSymbol = y;
  record.width = 4;
  appendEqualityRecord(refiner, record);

  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>{10, 11, 12, 13};
  bits[y] = std::vector<unsigned>{20, 21, 22, 23};

  RecordingSolver solver;
  // The candidate: the abstraction says unequal, while both operands hold
  // 0b0101. Nothing in a one-bit prefix can contradict that.
  solver.model[5] = false;
  solver.model[10] = true;
  solver.model[11] = false;
  solver.model[12] = true;
  solver.model[13] = false;
  solver.model[20] = true;
  solver.model[21] = false;
  solver.model[22] = true;
  solver.model[23] = false;

  EXPECT_EQ(1u, refiner.refine(solver, bits));
  // The prefix still grew -- the blocking clause is in addition to the
  // definition's progress, not instead of it.
  EXPECT_EQ(1u, refiner.equalities()[0].refinedBits);
  EXPECT_FALSE(refiner.equalities()[0].defined);
  EXPECT_TRUE(solver.someClauseBlocksModel());
}

// A defined equality's Boolean is exact, so transitivity chains are free
// to run through it. The word-level phase used to leave defined records
// out, which broke exactly the chains that mature first: a conflict whose
// path crossed one fell through to the bit-level scan and was rediscovered
// a definition at a time. Here x=y is already defined and true, y=z is
// asserted true, x!=z is asserted -- one congruence clause refutes the
// candidate without touching a bit, which the untouched refinedBits of the
// disequality's record is the witness for.
TEST_F(BVEQAbstractionTest, CongruenceChainsRunThroughDefinedEqualities)
{
  ASTNode x = makeSymbol("cc_x", 4);
  ASTNode y = makeSymbol("cc_y", 4);
  ASTNode z = makeSymbol("cc_z", 4);

  BVAbstractionRefiner refiner(&mgr);

  BVEQAbstraction xy;
  xy.eqNode = factory->CreateNode(EQ, x, y);
  xy.abstractionSATVar = 5;
  xy.leftSymbol = x;
  xy.rightSymbol = y;
  xy.width = 4;
  xy.defined = true;
  xy.refinedBits = 4;
  appendEqualityRecord(refiner, xy);

  BVEQAbstraction yz;
  yz.eqNode = factory->CreateNode(EQ, y, z);
  yz.abstractionSATVar = 6;
  yz.leftSymbol = y;
  yz.rightSymbol = z;
  yz.width = 4;
  appendEqualityRecord(refiner, yz);

  BVEQAbstraction xz;
  xz.eqNode = factory->CreateNode(EQ, x, z);
  xz.abstractionSATVar = 7;
  xz.leftSymbol = x;
  xz.rightSymbol = z;
  xz.width = 4;
  appendEqualityRecord(refiner, xz);

  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>{10, 11, 12, 13};
  bits[y] = std::vector<unsigned>{20, 21, 22, 23};
  bits[z] = std::vector<unsigned>{30, 31, 32, 33};

  RecordingSolver solver;
  // Unscripted bit variables read false, so all three operands hold zero:
  // every record is bit-level consistent or Case-B, and only the chain
  // through the defined x=y refutes the candidate at word level.
  solver.model[5] = true;
  solver.model[6] = true;
  solver.model[7] = false;

  EXPECT_EQ(1u, refiner.refine(solver, bits));
  EXPECT_EQ(0u, refiner.equalities()[2].refinedBits);
  EXPECT_FALSE(refiner.equalities()[2].defined);
  EXPECT_TRUE(solver.someClauseBlocksModel());
}

// A blocking round on a multiplication is one clause per result bit and
// nothing else: both operands' variables come out of the registry -- the
// blaster proxies constants too, pinning them by biconditionals -- so
// refinement has no variables to mint. It used to mint a fresh pinned
// vector for a constant operand on every round of the enumeration.
//
// The schemas are turned off for it. They are what a round spends *instead*
// of a blocking lemma, and this candidate contradicts one of them -- its
// first operand is a power of two -- so with them on there is no blocking
// round here to examine. The round that fires instead is the test below.
TEST_F(BVEQAbstractionTest, BlockingRoundReusesTheRegisteredConstant)
{
  mgr.UserFlags.bv_term_abstraction_schemas = false;

  ASTNode a = makeSymbol("mc_a", 4);
  ASTNode three = mgr.CreateBVConst(4, 3);
  ASTNode product = factory->CreateTerm(BVMULT, 4, a, three);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction record;
  record.termNode = product;
  record.opKind = BVMULT;
  record.operands[0] = a;
  record.operands[1] = three;
  record.numOperands = 2;
  record.width = 4;
  appendTermRecord(refiner, record);

  ToSATBase::ASTNodeToSATVar bits;
  bits[a] = std::vector<unsigned>{10, 11, 12, 13};
  bits[three] = std::vector<unsigned>{20, 21, 22, 23};
  bits[product] = std::vector<unsigned>{30, 31, 32, 33};

  RecordingSolver solver;
  // a = 2 and the proxies hold the constant's own value 3, as their
  // biconditionals force; the abstraction's result reads 0 where 2 * 3
  // is 6, so the round owes a blocking lemma. Every variable is scripted
  // explicitly, so the clause check below can evaluate whole clauses.
  const bool scripted[12] = {false, true, false, false,  // a = 0b0010
                             true,  true, false, false,  // proxies = 0b0011
                             false, false, false, false}; // result = 0
  for (unsigned i = 0; i < 4; i++)
  {
    solver.model[10 + i] = scripted[i];
    solver.model[20 + i] = scripted[4 + i];
    solver.model[30 + i] = scripted[8 + i];
  }

  EXPECT_EQ(1u, refiner.refine(solver, bits));
  EXPECT_EQ(1u, refiner.terms()[0].blockedRounds);
  EXPECT_EQ(0u, refiner.terms()[0].schemaRounds);
  EXPECT_FALSE(refiner.terms()[0].defined);
  EXPECT_EQ(0u, solver.newVarCalls);
  EXPECT_TRUE(solver.someClauseBlocksModel());
}

// The same candidate with the schemas left on, which is the default: the
// round is spent on the fact that a power-of-two operand turns the product
// into a shift, and not on ruling out the one pair of values.
//
// Both per-operation counters are checked, because they tell the two choices
// apart from outside: this one record gets a schema rather than a blocking
// lemma. The lemma still blocks the candidate, which is what refinement owes
// whoever called it, and it still mints nothing: the shift is written over
// the operand proxies and the abstraction's own result bits, all of which are
// already in the solver.
TEST_F(BVEQAbstractionTest, ASchemaRoundIsSpentWhereTheCandidateContradictsOne)
{
  ASTNode a = makeSymbol("ms_a", 4);
  ASTNode three = mgr.CreateBVConst(4, 3);
  ASTNode product = factory->CreateTerm(BVMULT, 4, a, three);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction record;
  record.termNode = product;
  record.opKind = BVMULT;
  record.operands[0] = a;
  record.operands[1] = three;
  record.numOperands = 2;
  record.width = 4;
  appendTermRecord(refiner, record);

  ToSATBase::ASTNodeToSATVar bits;
  bits[a] = std::vector<unsigned>{10, 11, 12, 13};
  bits[three] = std::vector<unsigned>{20, 21, 22, 23};
  bits[product] = std::vector<unsigned>{30, 31, 32, 33};

  RecordingSolver solver;
  // a = 2, the proxies hold the constant's own 3, and the result reads 0
  // where 2 * 3 is 6. Two is a power of two, so what the round owes is
  // "a = 2 -> t = 3 << 1" rather than "not (a = 2 and b = 3) -> t = 6".
  const bool scripted[12] = {false, true, false, false,  // a = 0b0010
                             true,  true, false, false,  // proxies = 0b0011
                             false, false, false, false}; // result = 0
  for (unsigned i = 0; i < 4; i++)
  {
    solver.model[10 + i] = scripted[i];
    solver.model[20 + i] = scripted[4 + i];
    solver.model[30 + i] = scripted[8 + i];
  }

  EXPECT_EQ(1u, refiner.refine(solver, bits));
  EXPECT_EQ(1u, refiner.terms()[0].schemaRounds);
  EXPECT_EQ(0u, refiner.terms()[0].blockedRounds);
  EXPECT_FALSE(refiner.terms()[0].defined);
  EXPECT_EQ(0u, solver.newVarCalls);
  EXPECT_TRUE(solver.someClauseBlocksModel());
}

// The public refinement-round counter counts calls that installed at least
// one constraint, while the two lemma counters count operations. One call can
// therefore increment both: the first product below contradicts a power-of-
// two schema, while the second has no violated schema and needs a blocking
// lemma. This is why the lemma counters do not partition refinement rounds.
TEST_F(BVEQAbstractionTest, OnePassCanInstallBothKindsOfMultiplicationLemma)
{
  ASTNode a = makeSymbol("mix_a", 4);
  ASTNode b = makeSymbol("mix_b", 4);
  ASTNode firstProduct = factory->CreateTerm(BVMULT, 4, a, b);
  ASTNode c = makeSymbol("mix_c", 4);
  ASTNode d = makeSymbol("mix_d", 4);
  ASTNode secondProduct = factory->CreateTerm(BVMULT, 4, c, d);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction first;
  first.termNode = firstProduct;
  first.opKind = BVMULT;
  first.operands[0] = a;
  first.operands[1] = b;
  first.numOperands = 2;
  first.width = 4;
  appendTermRecord(refiner, first);

  BVTermAbstraction second;
  second.termNode = secondProduct;
  second.opKind = BVMULT;
  second.operands[0] = c;
  second.operands[1] = d;
  second.numOperands = 2;
  second.width = 4;
  appendTermRecord(refiner, second);

  ToSATBase::ASTNodeToSATVar bits;
  bits[a] = std::vector<unsigned>{10, 11, 12, 13};
  bits[b] = std::vector<unsigned>{20, 21, 22, 23};
  bits[firstProduct] = std::vector<unsigned>{30, 31, 32, 33};
  bits[c] = std::vector<unsigned>{40, 41, 42, 43};
  bits[d] = std::vector<unsigned>{50, 51, 52, 53};
  bits[secondProduct] = std::vector<unsigned>{60, 61, 62, 63};

  RecordingSolver solver;
  // First: 2 * 3 is 6, not the candidate zero. The power-of-two operand
  // earns a schema. Second: 3 * 5 is 15, not the candidate one; both operands
  // and both products are odd, so every applicable algebraic fact already
  // holds and the candidate needs an ordinary blocking lemma.
  const bool scripted[24] = {
      false, true,  false, false, // a = 2
      true,  true,  false, false, // b = 3
      false, false, false, false, // first candidate = 0
      true,  true,  false, false, // c = 3
      true,  false, true,  false, // d = 5
      true,  false, false, false  // second candidate = 1
  };
  for (unsigned i = 0; i < 4; ++i)
  {
    solver.model[10 + i] = scripted[i];
    solver.model[20 + i] = scripted[4 + i];
    solver.model[30 + i] = scripted[8 + i];
    solver.model[40 + i] = scripted[12 + i];
    solver.model[50 + i] = scripted[16 + i];
    solver.model[60 + i] = scripted[20 + i];
  }

  EXPECT_EQ(2u, refiner.refine(solver, bits));
  EXPECT_EQ(1u, mgr.UserFlags.coverage.bv_refinement_rounds);
  EXPECT_EQ(1u, mgr.UserFlags.coverage.bv_schema_lemmas);
  EXPECT_EQ(1u, mgr.UserFlags.coverage.bv_blocking_lemmas);
  EXPECT_TRUE(solver.someClauseBlocksModel());
}

// maxPrecision's auxiliary SAT queries must not themselves be abstracted:
// a refinement round answers SOLVER_UNDECIDED, which its result handling
// reads as "error from solver" and aborts on. The entry points clear the
// two flags for their own scope and restore them on the way out, so a
// query narrow enough to abstract at this floor still runs exact inside.
TEST_F(BVEQAbstractionTest, MaxPrecisionRunsExactUnderAbstractionFlags)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 1;

  simplifier::constantBitP::FixedBits a(4, false);
  simplifier::constantBitP::FixedBits b(4, false);
  simplifier::constantBitP::FixedBits out(4, false);
  std::vector<simplifier::constantBitP::FixedBits*> children = {&a, &b};

  const bool noSolution =
      simplifier::constantBitP::maxPrecision(children, out, BVMULT, &mgr);

  // An unconstrained multiplication has solutions, and none of its bits is
  // common to all of them.
  EXPECT_FALSE(noSolution);
  EXPECT_EQ(0, out.countFixed());
  EXPECT_TRUE(mgr.UserFlags.bv_eq_abstraction);
  EXPECT_TRUE(mgr.UserFlags.bv_term_abstraction);
}

// The batch lowering is the party that has to make that freeze happen,
// after the CNF lands in the backend and before the first solve. No arrays
// and no array-equality context here, so every setFrozen this run performs
// is the abstraction's own: the equality's Boolean plus both 256-bit
// operands' bits.
TEST_F(BVEQAbstractionTest, BatchLoweringFreezesAbstractionVariables)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode x = makeSymbol("bf_x", 256);
  ASTNode y = makeSymbol("bf_y", 256);
  ASTNode eq = factory->CreateNode(EQ, x, y);

  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  ArrayTransformer at(&mgr, &simp);
  ToSATAIG tosat(&mgr, &at);

  RecordingSolver solver;
  EXPECT_TRUE(tosat.CallSAT(solver, eq, true));
  EXPECT_TRUE(tosat.hasBVEQAbstractions());
  EXPECT_GE(solver.frozen.size(), 513u);
}

TEST_F(BVEQAbstractionTest, RefusesAnEqualityWhoseOperandsAreNotEncoded)
{
  ASTNode x = makeSymbol("nb_x", 8);
  ASTNode y = makeSymbol("nb_y", 8);

  BVAbstractionRefiner refiner(&mgr);
  BVEQAbstraction record;
  record.eqNode = factory->CreateNode(EQ, x, y);
  record.abstractionSATVar = 1;
  record.leftSymbol = x;
  record.rightSymbol = y;
  record.width = 8;
  appendEqualityRecord(refiner, record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar empty;
  EXPECT_DEATH(refiner.refine(solver, empty), "did not encode");
}

TEST_F(BVEQAbstractionTest, RefusesAnEqualityRecordedWiderThanItsOperands)
{
  ASTNode x = makeSymbol("nw_x", 8);
  ASTNode y = makeSymbol("nw_y", 8);

  BVAbstractionRefiner refiner(&mgr);
  BVEQAbstraction record;
  record.eqNode = factory->CreateNode(EQ, x, y);
  record.abstractionSATVar = 1;
  record.leftSymbol = x;
  record.rightSymbol = y;
  record.width = 8;
  appendEqualityRecord(refiner, record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>(4, 2); // four bits for an eight-bit record
  bits[y] = std::vector<unsigned>(8, 3);
  EXPECT_DEATH(refiner.refine(solver, bits), "recorded wider");
}

TEST_F(BVEQAbstractionTest, RefusesAnEqualityBitThatNeverReachedTheCNF)
{
  ASTNode x = makeSymbol("nc_x", 8);
  ASTNode y = makeSymbol("nc_y", 8);

  BVAbstractionRefiner refiner(&mgr);
  BVEQAbstraction record;
  record.eqNode = factory->CreateNode(EQ, x, y);
  record.abstractionSATVar = 1;
  record.leftSymbol = x;
  record.rightSymbol = y;
  record.width = 8;
  appendEqualityRecord(refiner, record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar bits;
  std::vector<unsigned> partial(8, 2);
  partial[7] = BV_ABSTRACTION_NO_VAR;
  bits[x] = partial;
  bits[y] = std::vector<unsigned>(8, 3);
  EXPECT_DEATH(refiner.refine(solver, bits), "never reached the CNF");
}

TEST_F(BVEQAbstractionTest, RefusesAnAdditionWhoseOperandsAreNotEncoded)
{
  ASTNode x = makeSymbol("na_x", 8);
  ASTNode y = makeSymbol("na_y", 8);
  ASTNode sum = factory->CreateTerm(BVPLUS, 8, x, y);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction record;
  record.termNode = sum;
  record.opKind = BVPLUS;
  record.operands[0] = x;
  record.operands[1] = y;
  record.numOperands = 2;
  record.width = 8;
  appendTermRecord(refiner, record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar bits;
  // The abstraction's own result bits are there; the operands it stands for
  // are not, which is the half the scan reads to decide whether the candidate
  // contradicts it.
  bits[sum] = std::vector<unsigned>(8, 4);
  EXPECT_DEATH(refiner.refine(solver, bits), "did not encode");
}

TEST_F(BVEQAbstractionTest, RefusesAComparisonWithNoInputOfItsOwn)
{
  ASTNode x = makeSymbol("nk_x", 8);
  ASTNode y = makeSymbol("nk_y", 8);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction record;
  record.termNode = factory->CreateNode(BVSLT, x, y);
  record.opKind = BVSLT;
  record.operands[0] = x;
  record.operands[1] = y;
  record.numOperands = 2;
  record.width = 8;
  // condSATVar left at BV_ABSTRACTION_NO_VAR: the comparison's answer has
  // nowhere to be read from, so nothing about this candidate can be checked.
  appendTermRecord(refiner, record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>(8, 2);
  bits[y] = std::vector<unsigned>(8, 3);
  EXPECT_DEATH(refiner.refine(solver, bits), "no input carrying its answer");
}

} // namespace

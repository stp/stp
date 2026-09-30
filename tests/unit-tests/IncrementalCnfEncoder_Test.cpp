// SPDX-License-Identifier: MIT
#include "stp/Incremental/IncrementalCnfEncoder.h"
#include <gtest/gtest.h>

#include <unordered_map>
#include <unordered_set>

namespace
{
class ClauseCollector : public stp::SATSolver
{
  uint32_t variables = 0;

public:
  std::vector<std::vector<Lit>> clauses;
  bool okay() const override { return true; }
  uint8_t modelValue(uint32_t) const override { return undef_literal(); }
  uint32_t newVar() override { return variables++; }
  uint32_t nVars() const override { return variables; }
  void printStats() const override {}
  void setVerbosity(int) override {}
  lbool true_literal() const override { return 0; }
  lbool false_literal() const override { return 1; }
  lbool undef_literal() const override { return 2; }

protected:
  bool addClauseInternal(const vec_literals& clause) override
  {
    clauses.emplace_back();
    for (int i = 0; i < clause.size(); ++i)
      clauses.back().push_back(clause[i]);
    return true;
  }
  bool solveInternal(bool&) override { return false; }
};

class IncrementalCnfEncoderTest : public ::testing::Test
{
protected:
  Aig_Man_t* aig = Aig_ManStart(100);
  ClauseCollector solver;
  stp::IncrementalCnfEncoder encoder{&solver};

  ~IncrementalCnfEncoderTest() override { Aig_ManStop(aig); }

  bool evaluate(Aig_Obj_t* node, uint32_t assignment,
                std::unordered_map<unsigned, bool>& memo)
  {
    Aig_Obj_t* regular = Aig_Regular(node);
    auto hit = memo.find(Aig_ObjId(regular));
    bool value;
    if (hit != memo.end())
      value = hit->second;
    else
    {
      if (Aig_ObjIsConst1(regular))
        value = true;
      else if (Aig_ObjIsCi(regular))
      {
        const int var = encoder.varOf(regular);
        EXPECT_GE(var, 0);
        value = (assignment >> var) & 1;
      }
      else
      {
        const bool left = evaluate(Aig_ObjChild0(regular), assignment, memo);
        const bool right = evaluate(Aig_ObjChild1(regular), assignment, memo);
        value = left && right;
      }
      memo.emplace(Aig_ObjId(regular), value);
    }
    return value != bool(Aig_IsComplement(node));
  }

  // Enumerate every assignment to the emitted CNF, independently evaluating
  // the original AND circuit. All satisfying assignments must give the right
  // root, and every assignment to its inputs must have an extension.
  void checkTruthTable(Aig_Obj_t* root, const ClauseCollector& collected)
  {
    ASSERT_LT(collected.nVars(), 16u);
    unsigned satisfying = 0;
    unsigned inputs = 0;
    Aig_Obj_t* input;
    int i;
    Aig_ManForEachCi(aig, input, i) if (encoder.varOf(input) != -1)++ inputs;
    for (uint32_t assignment = 0; assignment < (1u << collected.nVars());
         ++assignment)
    {
      bool consistent = true;
      for (const auto& clause : collected.clauses)
      {
        bool satisfied = false;
        for (const auto literal : clause)
          satisfied |= bool((assignment >> stp::SATSolver::var(literal)) & 1) !=
                       stp::SATSolver::sign(literal);
        consistent &= satisfied;
      }
      if (!consistent)
        continue;
      ++satisfying;
      std::unordered_map<unsigned, bool> memo;
      const bool expected = evaluate(root, assignment, memo);
      const bool actual =
          bool((assignment >> encoder.varOf(Aig_Regular(root))) & 1) !=
          bool(Aig_IsComplement(root));
      EXPECT_EQ(expected, actual);
    }
    EXPECT_EQ(1u << inputs, satisfying);
  }

  uint64_t coneMass(std::vector<Aig_Obj_t*> pending)
  {
    std::unordered_set<unsigned> seen;
    uint64_t mass = 0;
    while (!pending.empty())
    {
      Aig_Obj_t* node = Aig_Regular(pending.back());
      pending.pop_back();
      if (seen.insert(Aig_ObjId(node)).second)
        mass += encoder.appendEncodedInputs(node, pending);
    }
    return mass;
  }
};

TEST_F(IncrementalCnfEncoderTest, MuxPolaritiesAndLateIntermediateRoots)
{
  Aig_Obj_t* condition = Aig_ObjCreateCi(aig);
  Aig_Obj_t* yes = Aig_ObjCreateCi(aig);
  Aig_Obj_t* no = Aig_ObjCreateCi(aig);
  for (unsigned polarity = 0; polarity < 8; ++polarity)
  {
    SCOPED_TRACE(polarity);
    ClauseCollector fresh;
    encoder.reset(&fresh);
    Aig_Obj_t* root = Aig_Mux(aig, Aig_NotCond(condition, bool(polarity & 1)),
                              Aig_NotCond(yes, bool(polarity & 2)),
                              Aig_NotCond(no, bool(polarity & 4)));
    Aig_Obj_t* regular = Aig_Regular(root);
    encoder.ensureEncoded(regular);
    EXPECT_EQ(4u, fresh.nVars());
    EXPECT_EQ(6u, fresh.submittedClauses());
    EXPECT_EQ(fresh.submittedClauses(), coneMass({regular}));
    const int rootVar = encoder.varOf(regular);
    const uint64_t generation = encoder.generation();
    encoder.ensureEncoded(regular);
    EXPECT_EQ(generation, encoder.generation());
    EXPECT_EQ(6u, fresh.submittedClauses());

    // Another assertion can name the intermediate AND that recovery skipped.
    // Its new definition must agree with the already encoded cell, whose
    // literal remains stable. Exercise both before checking the truth table.
    encoder.ensureEncoded(Aig_ObjFanin0(regular));
    encoder.ensureEncoded(Aig_ObjFanin1(regular));
    EXPECT_EQ(rootVar, encoder.varOf(regular));
    EXPECT_EQ(
        fresh.submittedClauses(),
        coneMass({regular, Aig_ObjFanin0(regular), Aig_ObjFanin1(regular)}));
    checkTruthTable(root, fresh);
    checkTruthTable(Aig_Not(root), fresh);
  }
}

TEST_F(IncrementalCnfEncoderTest, XorPolaritiesAndPreviouslyEncodedIntermediate)
{
  Aig_Obj_t* a = Aig_ObjCreateCi(aig);
  Aig_Obj_t* b = Aig_ObjCreateCi(aig);
  for (unsigned polarity = 0; polarity < 4; ++polarity)
  {
    SCOPED_TRACE(polarity);
    ClauseCollector fresh;
    encoder.reset(&fresh);
    Aig_Obj_t* root = Aig_Exor(aig, Aig_NotCond(a, bool(polarity & 1)),
                               Aig_NotCond(b, bool(polarity & 2)));
    Aig_Obj_t* regular = Aig_Regular(root);
    encoder.ensureEncoded(regular);
    EXPECT_EQ(3u, fresh.nVars());
    EXPECT_EQ(4u, fresh.submittedClauses());
    EXPECT_EQ(fresh.submittedClauses(), coneMass({regular}));
    encoder.ensureEncoded(Aig_ObjFanin0(regular));
    const int intermediateVar = encoder.varOf(Aig_ObjFanin0(regular));
    encoder.ensureEncoded(regular);
    EXPECT_EQ(intermediateVar, encoder.varOf(Aig_ObjFanin0(regular)));
    checkTruthTable(root, fresh);

    ClauseCollector other;
    encoder.reset(&other);
    // The root can also arrive after its intermediate gate was encoded.
    encoder.ensureEncoded(Aig_ObjFanin1(regular));
    const int priorVar = encoder.varOf(Aig_ObjFanin1(regular));
    encoder.ensureEncoded(regular);
    EXPECT_EQ(priorVar, encoder.varOf(Aig_ObjFanin1(regular)));
    checkTruthTable(root, other);
  }
}

TEST_F(IncrementalCnfEncoderTest, ConstantAndOrdinaryAnd)
{
  Aig_Obj_t* a = Aig_ObjCreateCi(aig);
  Aig_Obj_t* b = Aig_ObjCreateCi(aig);
  Aig_Obj_t* root = Aig_And(aig, Aig_Not(a), b);
  encoder.ensureEncoded(Aig_Regular(root));
  EXPECT_EQ(3u, solver.submittedClauses());
  EXPECT_EQ(3u, coneMass({root}));
  checkTruthTable(root, solver);
  encoder.ensureEncoded(Aig_ManConst1(aig));
  EXPECT_EQ(4u, solver.submittedClauses());
  EXPECT_EQ(4u, coneMass({root, Aig_ManConst1(aig)}));
  checkTruthTable(root, solver);
}

TEST_F(IncrementalCnfEncoderTest, MuxRecoveryCanKeepXorDecisionVariables)
{
  encoder.setRecoverCells(true, false);
  Aig_Obj_t* a = Aig_ObjCreateCi(aig);
  Aig_Obj_t* b = Aig_ObjCreateCi(aig);
  Aig_Obj_t* c = Aig_ObjCreateCi(aig);
  Aig_Obj_t* parity = Aig_Exor(aig, a, b);
  encoder.ensureEncoded(Aig_Regular(parity));
  EXPECT_EQ(5u, solver.nVars());
  EXPECT_EQ(9u, solver.submittedClauses());
  checkTruthTable(parity, solver);
  Aig_Obj_t* mux = Aig_Mux(aig, a, b, c);
  encoder.ensureEncoded(Aig_Regular(mux));
  EXPECT_EQ(15u, solver.submittedClauses());
  EXPECT_EQ(solver.submittedClauses(), coneMass({parity, mux}));
  checkTruthTable(mux, solver);
}

TEST_F(IncrementalCnfEncoderTest, NestedCellsShareInputsAndSurviveReset)
{
  Aig_Obj_t* a = Aig_ObjCreateCi(aig);
  Aig_Obj_t* b = Aig_ObjCreateCi(aig);
  Aig_Obj_t* c = Aig_ObjCreateCi(aig);
  Aig_Obj_t* left = Aig_Mux(aig, a, b, c);
  Aig_Obj_t* right = Aig_Mux(aig, Aig_Not(a), c, Aig_Not(b));
  Aig_Obj_t* root = Aig_Exor(aig, left, right);
  encoder.ensureEncoded(Aig_Regular(left));
  const int leftVar = encoder.varOf(Aig_Regular(left));
  encoder.ensureEncoded(Aig_Regular(root));
  EXPECT_EQ(leftVar, encoder.varOf(Aig_Regular(left)));
  EXPECT_EQ(solver.submittedClauses(), coneMass({root}));
  checkTruthTable(root, solver);

  ClauseCollector replacement;
  encoder.reset(&replacement);
  EXPECT_EQ(-1, encoder.varOf(Aig_Regular(root)));
  encoder.ensureEncoded(Aig_Regular(root));
  checkTruthTable(root, replacement);
}

TEST_F(IncrementalCnfEncoderTest, ChangingRecoveryKeepsExistingDefinitions)
{
  Aig_Obj_t* a = Aig_ObjCreateCi(aig);
  Aig_Obj_t* b = Aig_ObjCreateCi(aig);
  Aig_Obj_t* c = Aig_ObjCreateCi(aig);
  Aig_Obj_t* first = Aig_Exor(aig, a, b);
  encoder.ensureEncoded(Aig_Regular(first));
  const int firstVar = encoder.varOf(Aig_Regular(first));
  encoder.setRecoverCells(false);
  Aig_Obj_t* second = Aig_Mux(aig, c, first, a);
  encoder.ensureEncoded(Aig_Regular(second));
  EXPECT_EQ(firstVar, encoder.varOf(Aig_Regular(first)));
  EXPECT_EQ(solver.submittedClauses(), coneMass({second}));
  checkTruthTable(second, solver);

  encoder.setRecoverCells(true);
  Aig_Obj_t* third = Aig_Exor(aig, second, c);
  encoder.ensureEncoded(Aig_Regular(third));
  EXPECT_EQ(solver.submittedClauses(), coneMass({third}));
  checkTruthTable(third, solver);
}
} // namespace

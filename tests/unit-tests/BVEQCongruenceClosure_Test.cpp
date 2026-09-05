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

#include "stp/STPManager/STPManager.h"
#include "stp/STPManager/STP.h"
#include "stp/ToSat/BVEQCongruenceClosure.h"
#include "stp/FloatBlaster/rounding_modes.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <set>
#include <vector>

using namespace stp;

namespace
{

class BVEQCCTest : public ::testing::Test
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

TEST_F(BVEQCCTest, TransitivityConflictDetected)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode a = makeSymbol("cc_a", 256);
  ASTNode b = makeSymbol("cc_b", 256);
  ASTNode c = makeSymbol("cc_c", 256);

  ASTNode eq_ab = factory->CreateNode(EQ, a, b);
  ASTNode eq_bc = factory->CreateNode(EQ, b, c);
  ASTNode neq_ac = factory->CreateNode(NOT, factory->CreateNode(EQ, a, c));

  // (= a b) & (= b c) & !(= a c) is UNSAT by transitivity
  ASTNode formula = factory->CreateNode(AND, eq_ab,
      factory->CreateNode(AND, eq_bc, neq_ac));

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

TEST_F(BVEQCCTest, ConsistentModelNoConflict)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode a = makeSymbol("cc2_a", 256);
  ASTNode b = makeSymbol("cc2_b", 256);
  ASTNode c = makeSymbol("cc2_c", 256);

  ASTNode eq_ab = factory->CreateNode(EQ, a, b);
  ASTNode eq_bc = factory->CreateNode(EQ, b, c);

  // (= a b) & (= b c) is SAT
  ASTNode formula = factory->CreateNode(AND, eq_ab, eq_bc);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQCCTest, LongerTransitivityChain)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode a = makeSymbol("ch_a", 256);
  ASTNode b = makeSymbol("ch_b", 256);
  ASTNode c = makeSymbol("ch_c", 256);
  ASTNode d = makeSymbol("ch_d", 256);

  ASTNode eq_ab = factory->CreateNode(EQ, a, b);
  ASTNode eq_bc = factory->CreateNode(EQ, b, c);
  ASTNode eq_cd = factory->CreateNode(EQ, c, d);
  ASTNode neq_ad = factory->CreateNode(NOT, factory->CreateNode(EQ, a, d));

  // a=b & b=c & c=d & !(a=d) is UNSAT by transitivity chain
  ASTNode formula = factory->CreateNode(AND,
      factory->CreateNode(AND, eq_ab, eq_bc),
      factory->CreateNode(AND, eq_cd, neq_ad));

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

TEST_F(BVEQCCTest, ManySymbolsInEquivalenceClasses)
{
  // 12 symbols in 3 equivalence classes of 4.
  // All within-class equalities hold; no cross-class equalities.
  // CC should find no conflicts and the formula should be SAT.
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  const unsigned numClasses = 3;
  const unsigned classSize = 4;
  std::vector<std::vector<ASTNode>> classes(numClasses);

  for (unsigned c = 0; c < numClasses; ++c)
    for (unsigned i = 0; i < classSize; ++i)
    {
      std::string name = "mc_" + std::to_string(c) + "_" + std::to_string(i);
      classes[c].push_back(makeSymbol(name.c_str(), 256));
    }

  // Chain equalities within each class: s0=s1, s1=s2, s2=s3
  ASTVec conjuncts;
  for (unsigned c = 0; c < numClasses; ++c)
    for (unsigned i = 0; i + 1 < classSize; ++i)
      conjuncts.push_back(
          factory->CreateNode(EQ, classes[c][i], classes[c][i + 1]));

  ASTNode formula = conjuncts[0];
  for (unsigned i = 1; i < conjuncts.size(); ++i)
    formula = factory->CreateNode(AND, formula, conjuncts[i]);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQCCTest, CrossClassDisequalityWithTransitivityConflict)
{
  // 3 classes: {a,b}, {c,d}, with a=b, c=d, b=c, but ¬(a=d).
  // b=c merges the two classes, so a=d by transitivity → UNSAT.
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 64;

  ASTNode a = makeSymbol("xc_a", 256);
  ASTNode b = makeSymbol("xc_b", 256);
  ASTNode c = makeSymbol("xc_c", 256);
  ASTNode d = makeSymbol("xc_d", 256);

  ASTNode formula = factory->CreateNode(AND,
      factory->CreateNode(AND,
          factory->CreateNode(EQ, a, b),
          factory->CreateNode(EQ, c, d)),
      factory->CreateNode(AND,
          factory->CreateNode(EQ, b, c),
          factory->CreateNode(NOT, factory->CreateNode(EQ, a, d))));

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

// ---------------------------------------------------------------------------
// The explanation a conflict is reported with, read directly off the class.
//
// Detecting the conflict is the easy half. The clause the closure hands the
// solver is the other half, and it is only sound if the equalities it names
// really do chain the disequality's two sides: the solver takes
// (~e1 | ... | ~ek | d) as a theorem, so an explanation that omits a link
// asserts an implication equality does not license and refutes satisfiable
// queries. These drive check() straight, because that is the only way to see
// the clause rather than the verdict it eventually produces.

// Records what was added instead of solving. Variable numbering matches what
// the tests hand in as satVar.
class RecordingSolver : public stp::SATSolver
{
public:
  std::vector<std::vector<stp::SATSolver::Lit>> clauses;

  bool okay() const override { return true; }
  uint8_t modelValue(uint32_t) const override { return undef_literal(); }
  uint32_t newVar() override { return vars++; }
  uint32_t nVars() const override { return vars; }
  void printStats() const override {}
  void setVerbosity(int) override {}
  lbool true_literal() const override { return 0; }
  lbool false_literal() const override { return 1; }
  lbool undef_literal() const override { return 2; }

protected:
  bool addClauseInternal(const vec_literals& ps) override
  {
    std::vector<stp::SATSolver::Lit> c;
    for (int i = 0; i < ps.size(); ++i)
      c.push_back(ps[i]);
    clauses.push_back(c);
    return true;
  }

  bool solveInternal(bool&) override { return false; }

private:
  uint32_t vars = 0;
};

// The clause as (satVar, negated) pairs, order-insensitive.
std::set<std::pair<unsigned, bool>> asLiteralSet(
    const std::vector<stp::SATSolver::Lit>& clause)
{
  std::set<std::pair<unsigned, bool>> out;
  for (stp::SATSolver::Lit l : clause)
    out.insert({stp::SATSolver::var(l), stp::SATSolver::sign(l)});
  return out;
}

// Whether the equalities named negatively in `clause` connect the two sides
// of the equality named positively -- that is, whether the clause is a
// theorem of equality. This is the property the closure owes the solver, and
// checking it rather than a literal-for-literal expectation is what makes
// these tests indifferent to which spanning tree the union-find happens to
// build.
bool clauseIsEntailed(const std::vector<stp::SATSolver::Lit>& clause,
                      const std::vector<stp::BVEQCongruenceClosure::EqInfo>& eqs)
{
  const stp::BVEQCongruenceClosure::EqInfo* conclusion = nullptr;
  std::vector<const stp::BVEQCongruenceClosure::EqInfo*> antecedents;

  for (stp::SATSolver::Lit l : clause)
  {
    const stp::BVEQCongruenceClosure::EqInfo* named = nullptr;
    for (const auto& eq : eqs)
      if (eq.satVar == stp::SATSolver::var(l))
        named = &eq;
    if (named == nullptr)
      return false; // names a variable that is no equality of ours
    if (stp::SATSolver::sign(l))
      antecedents.push_back(named);
    else if (conclusion == nullptr)
      conclusion = named;
    else
      return false; // two positive literals is not the shape we emit
  }

  if (conclusion == nullptr)
    return false;

  // Close the antecedents and see whether they reach the conclusion's sides.
  std::set<unsigned> reached{conclusion->left};
  bool grew = true;
  while (grew)
  {
    grew = false;
    for (const auto* a : antecedents)
    {
      if (reached.count(a->left) && !reached.count(a->right))
      {
        reached.insert(a->right);
        grew = true;
      }
      else if (reached.count(a->right) && !reached.count(a->left))
      {
        reached.insert(a->left);
        grew = true;
      }
    }
  }
  return reached.count(conclusion->right) > 0;
}

TEST(BVEQCCExplanation, ChainThroughAnEarlierMergeIsNamedInFull)
{
  // a=b then b=c, so c joins a class that already holds two terms. The merge
  // that brings c in is justified by b=c *and* by a=b, which is what puts b
  // and a together in the first place; naming only b=c would assert
  // (b=c) -> (a=c).
  stp::BVEQCongruenceClosure cc;
  RecordingSolver solver;

  const std::vector<stp::BVEQCongruenceClosure::EqInfo> eqs = {
      {0, 1, 10, true},   // a = b
      {1, 2, 11, true},   // b = c
      {0, 2, 12, false},  // a != c  <- the conflict
  };

  EXPECT_EQ(1u, cc.check(eqs, solver));
  ASSERT_EQ(1u, solver.clauses.size());

  const std::set<std::pair<unsigned, bool>> expected = {
      {10, true}, {11, true}, {12, false}};
  EXPECT_EQ(expected, asLiteralSet(solver.clauses[0]));
  EXPECT_TRUE(clauseIsEntailed(solver.clauses[0], eqs));
}

TEST(BVEQCCExplanation, MergeOrderDoesNotDropLinks)
{
  // The same three terms, with the two equalities the other way round, so
  // that the second merge attaches to a class built by the first from the
  // other end.
  stp::BVEQCongruenceClosure cc;
  RecordingSolver solver;

  const std::vector<stp::BVEQCongruenceClosure::EqInfo> eqs = {
      {1, 2, 20, true},   // b = c
      {0, 1, 21, true},   // a = b
      {0, 2, 22, false},  // a != c
  };

  EXPECT_EQ(1u, cc.check(eqs, solver));
  ASSERT_EQ(1u, solver.clauses.size());

  const std::set<std::pair<unsigned, bool>> expected = {
      {20, true}, {21, true}, {22, false}};
  EXPECT_EQ(expected, asLiteralSet(solver.clauses[0]));
}

TEST(BVEQCCExplanation, OnlyTheConnectingChainIsNamed)
{
  // An equality the model asserts but which lies off the path must not be
  // dragged in: a weaker clause is sound but blocks less of the search than
  // the conflict entitles it to.
  stp::BVEQCongruenceClosure cc;
  RecordingSolver solver;

  const std::vector<stp::BVEQCongruenceClosure::EqInfo> eqs = {
      {0, 1, 30, true},   // a = b
      {1, 2, 31, true},   // b = c
      {2, 3, 32, true},   // c = d, past the conflict's endpoints
      {0, 2, 33, false},  // a != c
  };

  EXPECT_EQ(1u, cc.check(eqs, solver));
  ASSERT_EQ(1u, solver.clauses.size());

  const std::set<std::pair<unsigned, bool>> expected = {
      {30, true}, {31, true}, {33, false}};
  EXPECT_EQ(expected, asLiteralSet(solver.clauses[0]));
}

TEST(BVEQCCExplanation, EveryClauseOverAStarIsEntailed)
{
  // A hub term equal to five others -- the shape a RoundingMode validity
  // constraint takes, where one symbol is asserted equal to several mode
  // constants at once -- with a disequality between two of the spokes. Every
  // spoke pair is checked, so this covers explanations that must turn a
  // corner at the hub rather than run straight up one branch.
  for (unsigned i = 0; i < 5; ++i)
    for (unsigned j = i + 1; j < 5; ++j)
    {
      stp::BVEQCongruenceClosure cc;
      RecordingSolver solver;

      std::vector<stp::BVEQCongruenceClosure::EqInfo> eqs;
      for (unsigned k = 0; k < 5; ++k)
        eqs.push_back({0, k + 1, 40 + k, true}); // hub = spoke_k
      eqs.push_back({i + 1, j + 1, 50, false});  // spoke_i != spoke_j

      EXPECT_EQ(1u, cc.check(eqs, solver));
      ASSERT_EQ(1u, solver.clauses.size());
      EXPECT_TRUE(clauseIsEntailed(solver.clauses[0], eqs))
          << "spokes " << i << " and " << j;

      // The path runs spoke_i - hub - spoke_j and no further.
      const std::set<std::pair<unsigned, bool>> expected = {
          {40 + i, true}, {40 + j, true}, {50, false}};
      EXPECT_EQ(expected, asLiteralSet(solver.clauses[0]))
          << "spokes " << i << " and " << j;
    }
}

TEST(BVEQCCExplanation, DisequalityAcrossClassesIsNotAConflict)
{
  stp::BVEQCongruenceClosure cc;
  RecordingSolver solver;

  const std::vector<stp::BVEQCongruenceClosure::EqInfo> eqs = {
      {0, 1, 60, true},   // a = b
      {2, 3, 61, true},   // c = d
      {0, 2, 62, false},  // a != c, and nothing joins the two classes
  };

  EXPECT_EQ(0u, cc.check(eqs, solver));
  EXPECT_TRUE(solver.clauses.empty());
}

// ---------------------------------------------------------------------------
// The query the explanation defect was found on.

TEST_F(BVEQCCTest, ThreeWayRoundingModeDistinctIsSatisfiable)
{
  // RoundingMode has five values and three pairwise distinct ones exist, so
  // this is satisfiable -- but only the abstraction's narrow width floor lets
  // the equality abstraction reach the five-bit carrier at all. Each of the
  // two symbols carries a validity constraint that is a disjunction of
  // equalities against the mode constants, so a candidate model asserts
  // several equalities through one hub term, and the disequalities the
  // distinct expands to are exactly the conflicts whose explanation has to
  // name the whole chain.
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 1;

  ASTNode x0 = mgr.CreateSourceSymbol("rm_x0", SourceSort::roundingMode());
  ASTNode x1 = mgr.CreateSourceSymbol("rm_x1", SourceSort::roundingMode());
  ASTNode rtz = mgr.CreateRMConst(symbolic_fp::ROUND_TOWARD_ZERO);

  ASTVec conjuncts;
  conjuncts.push_back(mgr.roundingModeValidConstraint(x0));
  conjuncts.push_back(mgr.roundingModeValidConstraint(x1));
  conjuncts.push_back(
      factory->CreateNode(NOT, factory->CreateNode(EQ, rtz, x1)));
  conjuncts.push_back(
      factory->CreateNode(NOT, factory->CreateNode(EQ, rtz, x0)));
  conjuncts.push_back(
      factory->CreateNode(NOT, factory->CreateNode(EQ, x1, x0)));

  ASTNode formula = factory->CreateNode(AND, conjuncts);

  STP stp(&mgr);
  EXPECT_EQ(SOLVER_INVALID, stp.TopLevelSTP(formula, mgr.ASTFalse));
}

TEST_F(BVEQCCTest, HubEqualitiesWithASpokeDisequalityStaySatisfiable)
{
  // The same shape without the floating-point vocabulary: a hub equal to one
  // of several terms, and two of those terms held apart. Satisfiable, and it
  // is satisfiable through the abstraction only if the transitivity clauses
  // name every equality they lean on.
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_abstraction_width = 1;

  ASTNode hub = makeSymbol("hub", 8);
  ASTNode s0 = makeSymbol("spoke0", 8);
  ASTNode s1 = makeSymbol("spoke1", 8);
  ASTNode s2 = makeSymbol("spoke2", 8);

  ASTNode formula = factory->CreateNode(
      AND,
      {factory->CreateNode(OR, factory->CreateNode(EQ, hub, s0),
                           factory->CreateNode(EQ, hub, s1),
                           factory->CreateNode(EQ, hub, s2)),
       factory->CreateNode(NOT, factory->CreateNode(EQ, s0, s1)),
       factory->CreateNode(NOT, factory->CreateNode(EQ, s1, s2)),
       factory->CreateNode(NOT, factory->CreateNode(EQ, s0, s2))});

  STP stp(&mgr);
  EXPECT_EQ(SOLVER_INVALID, stp.TopLevelSTP(formula, mgr.ASTFalse));
}

} // namespace

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

#include "stp/ToSat/BVEQCongruenceClosure.h"

#include <gtest/gtest.h>

#include <set>
#include <utility>
#include <vector>

using namespace stp;

namespace
{

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

} // namespace

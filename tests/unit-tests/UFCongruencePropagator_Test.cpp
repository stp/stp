/********************************************************************
 * The in-search congruence closure, driven the way a SAT backend drives it.
 *
 * AUTHORS: Trevor Hansen
 *
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
********************************************************************/

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFCongruencePropagator.h"
#include <gtest/gtest.h>
#include <algorithm>
#include <string>
#include <vector>

namespace
{

// The propagator is addressed in STP's literal encoding: 2*var for the
// positive literal, 2*var+1 for its negation.
uint32_t pos(unsigned var)
{
  return 2 * var;
}
uint32_t neg(unsigned var)
{
  return 2 * var + 1;
}

// A UFDecl is only ever compared by address here, so the tests need an
// address rather than a declaration.
const stp::UFDecl* declarationA()
{
  return reinterpret_cast<const stp::UFDecl*>(0x10);
}
const stp::UFDecl* declarationB()
{
  return reinterpret_cast<const stp::UFDecl*>(0x20);
}

// Distinct symbols to name terms with. The propagator only uses the nodes as
// map keys, so eight bits wide is as good as any.
class Terms
{
public:
  stp::ASTNode operator()(const std::string& name)
  {
    return manager_.CreateSymbol(name.c_str(), 0, 8);
  }

private:
  stp::STPMgr manager_;
};

std::vector<std::vector<uint32_t>> drain(stp::UFCongruencePropagator& p)
{
  std::vector<std::vector<uint32_t>> out;
  std::vector<uint32_t> clause;
  while (p.nextClause(clause))
    out.push_back(clause);
  return out;
}

bool holds(const std::vector<std::vector<uint32_t>>& clauses,
           std::vector<uint32_t> wanted)
{
  std::sort(wanted.begin(), wanted.end());
  for (std::vector<uint32_t> clause : clauses)
  {
    std::sort(clause.begin(), clause.end());
    if (clause == wanted)
      return true;
  }
  return false;
}

} // namespace

// a=b and b=c asserted: the closure owes the chain that joined them,
// negated, plus the atom the join has made true. Nothing has to deny it
// first -- that clause propagates a=c, which is what the eagerly encoded
// transitivity triples were there to do.
TEST(UFCongruencePropagator, AJoinPropagatesTheImpliedAtom)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned a = p.term(terms("a"));
  const unsigned b = p.term(terms("b"));
  const unsigned c = p.term(terms("c"));
  p.addAtom(a, b, pos(1));
  p.addAtom(b, c, pos(2));
  p.addAtom(a, c, pos(3));
  p.freeze(8);

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(1)});
  EXPECT_TRUE(drain(p).empty()) << "one edge implies nothing";

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(2)});
  const std::vector<std::vector<uint32_t>> clauses = drain(p);
  ASSERT_EQ(1u, clauses.size());
  EXPECT_TRUE(holds(clauses, {neg(1), neg(2), pos(3)}));
}

// The same clause is the conflict when the search has already denied the
// atom the join implies.
TEST(UFCongruencePropagator, AJoinRefutesADeniedAtom)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned a = p.term(terms("a"));
  const unsigned b = p.term(terms("b"));
  const unsigned c = p.term(terms("c"));
  p.addAtom(a, b, pos(1));
  p.addAtom(b, c, pos(2));
  p.addAtom(a, c, pos(3));
  p.freeze(8);

  p.notifyNewDecisionLevel();
  p.notifyAssignments({neg(3), pos(1)});
  EXPECT_TRUE(drain(p).empty());

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(2)});
  const std::vector<std::vector<uint32_t>> clauses = drain(p);
  ASSERT_EQ(1u, clauses.size());
  EXPECT_TRUE(holds(clauses, {neg(1), neg(2), pos(3)}))
      << "every literal false under this assignment";
}

// The chain may be walked in either direction and may reach past the two
// terms the denied atom names.
TEST(UFCongruencePropagator, TransitivityOverALongerChain)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  std::vector<unsigned> t;
  for (int i = 0; i < 5; i++)
    t.push_back(p.term(terms("t" + std::to_string(i))));
  for (unsigned i = 0; i + 1 < t.size(); i++)
    p.addAtom(t[i], t[i + 1], pos(i + 1)); // vars 1..4
  p.addAtom(t[0], t[4], pos(9));
  p.freeze(16);

  p.notifyNewDecisionLevel();
  p.notifyAssignments({neg(9)});
  EXPECT_TRUE(drain(p).empty());

  // Joined out of order, and the last one closes the chain.
  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(3), pos(1), pos(4)});
  EXPECT_TRUE(drain(p).empty());
  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(2)});
  const std::vector<std::vector<uint32_t>> clauses = drain(p);
  ASSERT_EQ(1u, clauses.size());
  EXPECT_TRUE(holds(clauses, {neg(1), neg(2), neg(3), neg(4), pos(9)}))
      << "the whole path, and only the path";
}

// A term that is only on a side branch of the proof forest is not on the
// path, and must not reach the clause.
TEST(UFCongruencePropagator, ExplanationExcludesSideBranches)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned a = p.term(terms("a"));
  const unsigned b = p.term(terms("b"));
  const unsigned c = p.term(terms("c"));
  const unsigned side = p.term(terms("side"));
  p.addAtom(a, b, pos(1));
  p.addAtom(b, c, pos(2));
  p.addAtom(b, side, pos(4)); // a branch off b, not on the a..c path
  p.addAtom(a, c, pos(3));
  p.freeze(8);

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(1), pos(4), pos(2), neg(3)});
  const std::vector<std::vector<uint32_t>> clauses = drain(p);
  ASSERT_EQ(1u, clauses.size());
  EXPECT_TRUE(holds(clauses, {neg(1), neg(2), pos(3)}));
}

// Undoing a level has to take back the joins made at it, so that a chain
// which no longer exists explains nothing.
TEST(UFCongruencePropagator, BacktrackUndoesJoins)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned a = p.term(terms("a"));
  const unsigned b = p.term(terms("b"));
  const unsigned c = p.term(terms("c"));
  p.addAtom(a, b, pos(1));
  p.addAtom(b, c, pos(2));
  p.addAtom(a, c, pos(3));
  p.freeze(8);

  p.notifyNewDecisionLevel(); // level 1
  p.notifyAssignments({pos(1)});
  p.notifyNewDecisionLevel(); // level 2
  p.notifyAssignments({pos(2)});
  ASSERT_EQ(1u, drain(p).size()) << "the join implies a = c";
  p.notifyBacktrack(1);       // b = c is gone, and so is the class

  // With the join undone there is no chain, so the atom the search now
  // denies contradicts nothing -- and the closure must not offer a clause
  // over an explanation that no longer exists.
  p.notifyNewDecisionLevel();
  p.notifyAssignments({neg(3)});
  EXPECT_TRUE(drain(p).empty()) << "a and c are no longer joined";
  EXPECT_EQ(1u, p.transitivityClauses());

  // The state is still usable: rejoining walks the same path again, and the
  // clause it would write is the one already given.
  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(2)});
  EXPECT_TRUE(drain(p).empty()) << "a repeat, dropped";
  EXPECT_EQ(1u, p.suppressedDuplicates());
}

// Backtracking to the root and replaying a different order must leave no
// trace of the first attempt.
TEST(UFCongruencePropagator, BacktrackToRootAndReplay)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned a = p.term(terms("a"));
  const unsigned b = p.term(terms("b"));
  const unsigned c = p.term(terms("c"));
  const unsigned d = p.term(terms("d"));
  p.addAtom(a, b, pos(1));
  p.addAtom(b, c, pos(2));
  p.addAtom(c, d, pos(3));
  p.addAtom(a, d, pos(4));
  p.freeze(8);

  for (int round = 0; round < 3; round++)
  {
    p.notifyNewDecisionLevel();
    p.notifyAssignments({pos(1)});
    p.notifyNewDecisionLevel();
    p.notifyAssignments({pos(2)});
    p.notifyNewDecisionLevel();
    p.notifyAssignments({pos(3)});
    p.notifyNewDecisionLevel();
    p.notifyAssignments({neg(4)});
    const std::vector<std::vector<uint32_t>> clauses = drain(p);
    // Only the first pass produces the clause: it is a consequence of the
    // query, so the backend keeps it and there is nothing to gain from
    // offering it again.
    if (round == 0)
    {
      ASSERT_EQ(1u, clauses.size());
      EXPECT_TRUE(holds(clauses, {neg(1), neg(2), neg(3), pos(4)}));
    }
    else
      EXPECT_TRUE(clauses.empty());
    p.notifyBacktrack(0);
  }
  EXPECT_EQ(1u, p.transitivityClauses());
}

// Two applications of one declaration whose arguments the search has driven
// together may not disagree on a result bit.
TEST(UFCongruencePropagator, CongruenceOverJoinedArguments)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned x = p.term(terms("x"));
  const unsigned y = p.term(terms("y"));
  p.addAtom(x, y, pos(1));
  // f(x) has result bits 10,11; f(y) has 12,13.
  p.addApplication(declarationA(), {x}, {10, 11});
  p.addApplication(declarationA(), {y}, {12, 13});
  p.freeze(16);

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(10), neg(12)}); // bit 0 already disagrees
  EXPECT_TRUE(drain(p).empty()) << "the arguments are not joined yet";

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(1)});
  const std::vector<std::vector<uint32_t>> clauses = drain(p);
  ASSERT_EQ(1u, clauses.size());
  EXPECT_TRUE(holds(clauses, {neg(1), neg(10), pos(12)}));
  EXPECT_EQ(1u, p.congruenceClauses());
}

// Congruence needs every argument joined, not just one of them.
TEST(UFCongruencePropagator, CongruenceNeedsEveryArgument)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned x1 = p.term(terms("x1"));
  const unsigned x2 = p.term(terms("x2"));
  const unsigned y1 = p.term(terms("y1"));
  const unsigned y2 = p.term(terms("y2"));
  p.addAtom(x1, y1, pos(1));
  p.addAtom(x2, y2, pos(2));
  p.addApplication(declarationA(), {x1, x2}, {10});
  p.addApplication(declarationA(), {y1, y2}, {11});
  p.freeze(16);

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(1), pos(10), neg(11)});
  EXPECT_TRUE(drain(p).empty()) << "the second argument is still apart";

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(2)});
  const std::vector<std::vector<uint32_t>> clauses = drain(p);
  ASSERT_EQ(1u, clauses.size());
  EXPECT_TRUE(holds(clauses, {neg(1), neg(2), neg(10), pos(11)}));
}

// Applications of different declarations are never congruent however their
// arguments line up.
TEST(UFCongruencePropagator, DifferentDeclarationsAreNeverCongruent)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned x = p.term(terms("x"));
  const unsigned y = p.term(terms("y"));
  p.addAtom(x, y, pos(1));
  // Two of each, so neither declaration is dropped as having only one.
  p.addApplication(declarationA(), {x}, {10});
  p.addApplication(declarationA(), {x}, {14});
  p.addApplication(declarationB(), {y}, {11});
  p.addApplication(declarationB(), {y}, {15});
  p.freeze(16);

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(1), pos(10), neg(11), pos(14), neg(15)});
  EXPECT_TRUE(drain(p).empty());
  EXPECT_EQ(0u, p.congruenceClauses());
}

// An atom carried by a negated literal -- a one-bit equality against a zero
// constant is the other operand's bit, negated -- reads the other way round.
TEST(UFCongruencePropagator, NegatedAtomLiteralAssertsEquality)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned a = p.term(terms("a"));
  const unsigned b = p.term(terms("b"));
  const unsigned c = p.term(terms("c"));
  p.addAtom(a, b, neg(1)); // a = b exactly when variable 1 is false
  p.addAtom(b, c, pos(2));
  p.addAtom(a, c, pos(3));
  p.freeze(8);

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(1)}); // that denies a = b
  p.notifyAssignments({pos(2), neg(3)});
  EXPECT_TRUE(drain(p).empty()) << "a and b were never joined";

  p.notifyBacktrack(0);
  p.notifyNewDecisionLevel();
  p.notifyAssignments({neg(1), pos(2), neg(3)});
  const std::vector<std::vector<uint32_t>> clauses = drain(p);
  ASSERT_EQ(1u, clauses.size());
  EXPECT_TRUE(holds(clauses, {pos(1), neg(2), pos(3)}));
}

// An assignment notified twice -- which chronological backtracking makes the
// backend do -- must not join anything twice or corrupt the undo stack.
TEST(UFCongruencePropagator, RepeatedNotificationIsIdempotent)
{
  Terms terms;
  stp::UFCongruencePropagator p;
  const unsigned a = p.term(terms("a"));
  const unsigned b = p.term(terms("b"));
  const unsigned c = p.term(terms("c"));
  p.addAtom(a, b, pos(1));
  p.addAtom(b, c, pos(2));
  p.addAtom(a, c, pos(3));
  p.freeze(8);

  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(1)});
  p.notifyAssignments({pos(1), pos(1)});
  p.notifyNewDecisionLevel();
  p.notifyAssignments({pos(2)});
  p.notifyAssignments({pos(2)});
  // Repeats join nothing twice, so exactly one implied atom is reported.
  ASSERT_EQ(1u, drain(p).size());
  EXPECT_EQ(1u, p.merges() - 1u) << "two joins, and no more";

  p.notifyBacktrack(1);
  p.notifyNewDecisionLevel();
  p.notifyAssignments({neg(3)});
  EXPECT_TRUE(drain(p).empty()) << "one join was undone, so no chain remains";
}

// Nothing to reason over is reported as such, so the caller can leave the
// backend unencumbered.
TEST(UFCongruencePropagator, WorthConnectingNeedsAtoms)
{
  Terms terms;
  stp::UFCongruencePropagator empty;
  empty.freeze(4);
  EXPECT_FALSE(empty.worthConnecting());

  stp::UFCongruencePropagator withAtom;
  const unsigned a = withAtom.term(terms("a"));
  const unsigned b = withAtom.term(terms("b"));
  withAtom.addAtom(a, b, pos(1));
  withAtom.freeze(4);
  EXPECT_TRUE(withAtom.worthConnecting());
  const std::vector<unsigned>& observed = withAtom.observedVariables();
  EXPECT_EQ(1u, observed.size());
  EXPECT_EQ(1u, observed[0]);
}

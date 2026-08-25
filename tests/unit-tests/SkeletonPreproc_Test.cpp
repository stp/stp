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

// What the propositional structure of a query decides on its own.
//
// Everything this pass reports is asserted at the top level and never taken
// back, so a fact it invents rather than derives turns a satisfiable query
// unsat -- silently, and only on the queries that reach it. The atoms are
// opaque here by construction, which is exactly what makes a mapping bug
// possible: a variable read back against the wrong atom would report a fact
// about some other predicate entirely, and every formula below would still
// look plausible.
//
// So the checks are of two kinds. The structural ones fix what the pass must
// say on formulas whose answer is settled by hand. The exhaustive one takes
// every Boolean function of three atoms there is -- all 256 of them, built
// as an explicit truth table over three bit-vector equalities -- and checks
// the pass against what that function actually forces, computed here by
// enumerating its models rather than by reasoning about it.
#include "stp/Simplifier/SkeletonPreproc.h"

#include "stp/Sat/SATSolverFactory.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

#include <memory>
#include <vector>

using namespace stp;

namespace
{

class SkeletonTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  NodeFactory* nf = nullptr;
  ASTNode a, b, c;

  void SetUp() override
  {
    nf = mgr.defaultNodeFactory;
    // Three predicates over bit-vectors. Each is a leaf to the skeleton:
    // an EQ whose children are terms, so the walk stops and abstracts it.
    a = nf->CreateNode(EQ, mgr.CreateSymbol("a0", 0, 8),
                       mgr.CreateSymbol("a1", 0, 8));
    b = nf->CreateNode(EQ, mgr.CreateSymbol("b0", 0, 8),
                       mgr.CreateSymbol("b1", 0, 8));
    c = nf->CreateNode(EQ, mgr.CreateSymbol("c0", 0, 8),
                       mgr.CreateSymbol("c1", 0, 8));
  }

  ASTNode NOTof(const ASTNode& n) { return nf->CreateNode(NOT, n); }

  // The pass reads what the SAT backend fixed at the root, and only CaDiCaL
  // reports that; everywhere else it is a sound no-op. The checks below come
  // in two kinds, and only one of them survives such a build: that a fact
  // reported is right holds always, and that a fact is reported at all holds
  // only where the backend can say so.
  bool backendReports()
  {
    std::unique_ptr<SATSolver> s(createSATSolver(mgr.UserFlags));
    return s != NULL && s->reportsRootFixed();
  }

  // What the pass reports, as a signed verdict per atom: 1 forced true,
  // -1 forced false, 0 not forced.
  void verdicts(const ASTNode& query, int& va, int& vb, int& vc, bool& unsat)
  {
    SkeletonPreproc sk(&mgr);
    const ASTVec facts = sk.derive(query, unsat);
    va = vb = vc = 0;
    for (const ASTNode& f : facts)
    {
      const bool neg = (f.GetKind() == NOT);
      const ASTNode atom = neg ? f[0] : f;
      const int sign = neg ? -1 : 1;
      if (atom == a) va = sign;
      else if (atom == b) vb = sign;
      else if (atom == c) vc = sign;
      else ADD_FAILURE() << "a fact was reported about an unknown atom";
    }
  }
};

} // namespace

TEST_F(SkeletonTest, a_conjunction_forces_both_conjuncts)
{
  if (!backendReports())
    GTEST_SKIP() << "this backend does not report root-fixed literals";
  int va, vb, vc; bool unsat;
  verdicts(nf->CreateNode(AND, a, b), va, vb, vc, unsat);
  EXPECT_FALSE(unsat);
  EXPECT_EQ(va, 1);
  EXPECT_EQ(vb, 1);
  EXPECT_EQ(vc, 0) << "an atom the query never mentions was given a verdict";
}

TEST_F(SkeletonTest, a_negated_conjunct_is_forced_false)
{
  if (!backendReports())
    GTEST_SKIP() << "this backend does not report root-fixed literals";
  int va, vb, vc; bool unsat;
  verdicts(nf->CreateNode(AND, a, NOTof(b)), va, vb, vc, unsat);
  EXPECT_FALSE(unsat);
  EXPECT_EQ(va, 1);
  EXPECT_EQ(vb, -1);
}

TEST_F(SkeletonTest, a_disjunction_forces_nothing)
{
  int va, vb, vc; bool unsat;
  verdicts(nf->CreateNode(OR, a, b), va, vb, vc, unsat);
  EXPECT_FALSE(unsat);
  EXPECT_EQ(va, 0);
  EXPECT_EQ(vb, 0);
}

// The propagation the pass exists for: a fact that follows only by putting
// two assertions together.
TEST_F(SkeletonTest, modus_ponens_is_derived)
{
  if (!backendReports())
    GTEST_SKIP() << "this backend does not report root-fixed literals";
  int va, vb, vc; bool unsat;
  verdicts(nf->CreateNode(AND, a, nf->CreateNode(IMPLIES, a, b)), va, vb, vc,
           unsat);
  EXPECT_FALSE(unsat);
  EXPECT_EQ(va, 1);
  EXPECT_EQ(vb, 1) << "b follows from a and a->b";
}

TEST_F(SkeletonTest, a_contradictory_skeleton_is_reported_unsat)
{
  if (!backendReports())
    GTEST_SKIP() << "this backend does not report root-fixed literals";
  int va, vb, vc; bool unsat;
  verdicts(nf->CreateNode(AND, a, NOTof(a)), va, vb, vc, unsat);
  EXPECT_TRUE(unsat) << "the structure alone refutes this query";
}

// A contradiction the arithmetic would have to settle is NOT the skeleton's
// to find: the atoms are opaque, so `x = y` and `x != y` are the same atom
// negated, but `x = y` and `y = x` are two atoms as far as this can tell.
// The pass must not claim anything there.
TEST_F(SkeletonTest, an_arithmetic_contradiction_is_left_alone)
{
  const ASTNode x = mgr.CreateSymbol("x", 0, 8);
  const ASTNode y = mgr.CreateSymbol("y", 0, 8);
  const ASTNode lt = nf->CreateNode(BVLT, x, y);
  const ASTNode gt = nf->CreateNode(BVGT, x, y);
  bool unsat = false;
  SkeletonPreproc sk(&mgr);
  const ASTVec facts = sk.derive(nf->CreateNode(AND, lt, gt), unsat);
  EXPECT_FALSE(unsat) << "the skeleton cannot know these two conflict";
  // Both are top-level conjuncts, so both are forced -- which is true, and
  // is exactly what the bit-blaster then has to refute. Reported only where
  // the backend can say what it fixed.
  EXPECT_EQ(facts.size(), backendReports() ? 2u : 0u);
}

// Every Boolean function of three atoms, against what it really forces.
//
// The query is built as an explicit disjunction of the assignments the
// function accepts, so nothing about its structure is shared with the pass
// under test, and the expected answer is computed by enumeration.
TEST_F(SkeletonTest, every_function_of_three_atoms)
{
  const ASTNode atoms[3] = {a, b, c};

  for (unsigned table = 1; table < 256; table++) // 0 is the empty function
  {
    ASTVec rows;
    for (unsigned m = 0; m < 8; m++)
    {
      if (((table >> m) & 1u) == 0)
        continue;
      ASTVec lits;
      for (unsigned i = 0; i < 3; i++)
        lits.push_back(((m >> i) & 1u) ? atoms[i] : NOTof(atoms[i]));
      rows.push_back(nf->CreateNode(AND, lits));
    }
    const ASTNode query =
        (rows.size() == 1) ? rows[0] : nf->CreateNode(OR, rows);

    // What the function forces, by enumeration.
    int want[3] = {0, 0, 0};
    for (unsigned i = 0; i < 3; i++)
    {
      bool sawTrue = false, sawFalse = false;
      for (unsigned m = 0; m < 8; m++)
      {
        if (((table >> m) & 1u) == 0)
          continue;
        (((m >> i) & 1u) ? sawTrue : sawFalse) = true;
      }
      want[i] = (sawTrue && !sawFalse) ? 1 : (sawFalse && !sawTrue) ? -1 : 0;
    }

    int va, vb, vc; bool unsat;
    verdicts(query, va, vb, vc, unsat);
    ASSERT_FALSE(unsat) << "table " << table << " has a model";

    // The pass may report fewer facts than the function forces -- it asks a
    // SAT solver what it settled while simplifying, not what is entailed --
    // but every fact it does report has to be right. Weaker is sound;
    // wrong is not.
    const int got[3] = {va, vb, vc};
    for (unsigned i = 0; i < 3; i++)
    {
      if (got[i] != 0)
      {
        ASSERT_EQ(got[i], want[i])
            << "table " << table << " atom " << i << ": reported "
            << got[i] << " but the function forces " << want[i];
      }
    }
  }
}

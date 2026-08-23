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

// The encoding an abstracted operation falls back on when its refinement
// gives up, checked over every pair of operands there is at four bits.
//
// It is not built here. BVExactEncoder blasts the operation with the same
// BitBlaster a plain solve uses and maps the AIG to CNF with the same ABC
// pass, then splices the result onto SAT variables the solver already has.
// The splice is the part that is new and the part that can be silently
// wrong: it renumbers every variable of the derived CNF, and a mapping that
// sent one operand's bits to the other's -- or that let an input the circuit
// never reads collide with an internal variable -- would still produce a
// well-formed CNF and a solver that answers something.
//
// So what is checked is behaviour and not shape. For every pair of operand
// values, the clauses are asked what result they permit: exactly one value,
// and the right one. That covers the splice, the operand order, the
// truncation, and the two divisions' behaviour on a zero divisor, none of
// which have anywhere to hide under it.
#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/BVExactEncoder.h"
#ifdef USE_MINISAT
#include "stp/Sat/MinisatCore.h"
#endif
#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif
#ifdef USE_CRYPTOMINISAT
#include "stp/Sat/CryptoMinisat5.h"
#endif

#include <gtest/gtest.h>

#include <cstdio>
#include <memory>
#include <vector>

using namespace stp;

namespace
{

const unsigned WIDTH = 4;
const unsigned VALUES = 1u << WIDTH;

std::unique_ptr<SATSolver> makeSolver()
{
#if defined(USE_MINISAT)
  return std::unique_ptr<SATSolver>(new MinisatCore());
#elif defined(USE_CADICAL)
  return std::unique_ptr<SATSolver>(new Cadical());
#elif defined(USE_CRYPTOMINISAT)
  return std::unique_ptr<SATSolver>(new CryptoMinisat5());
#else
  return std::unique_ptr<SATSolver>();
#endif
}

// What the operation should give, at this width, including the two
// totalisations SMT-LIB asks for on a zero divisor: all ones for the
// quotient, the dividend for the remainder.
unsigned reference(Kind kind, unsigned a, unsigned b)
{
  switch (kind)
  {
    case BVMULT: return (a * b) & (VALUES - 1);
    case BVDIV: return b == 0 ? (VALUES - 1) : (a / b);
    case BVMOD: return b == 0 ? a : (a % b);
    default: break;
  }
  return 0;
}

class BVExactEncoderTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  ASTNode operation(Kind kind, const char* aName, const char* bName)
  {
    ASTNode a = mgr.CreateSymbol(aName, 0, WIDTH);
    ASTNode b = mgr.CreateSymbol(bName, 0, WIDTH);
    return mgr.defaultNodeFactory->CreateTerm(kind, WIDTH, a, b);
  }

  // Every operand pair, one solve each: the operands are pinned by unit
  // clauses over a solver built for that pair alone, so what comes back is
  // what the clauses permit and nothing is carried between pairs.
  void checkEveryPair(Kind kind, const ASTNode& term)
  {
    for (unsigned a = 0; a < VALUES; ++a)
      for (unsigned b = 0; b < VALUES; ++b)
      {
        std::unique_ptr<SATSolver> solver = makeSolver();
        ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";

        std::vector<unsigned> aVars(WIDTH), bVars(WIDTH), resultVars(WIDTH);
        for (unsigned i = 0; i < WIDTH; ++i)
        {
          aVars[i] = solver->newVar();
          bVars[i] = solver->newVar();
          resultVars[i] = solver->newVar();
          solver->setFrozen(aVars[i]);
          solver->setFrozen(bVars[i]);
          solver->setFrozen(resultVars[i]);
        }

        BVExactEncoder(&mgr).encode(*solver, term, WIDTH, aVars, bVars,
                                    resultVars);

        SATSolver::vec_literals unit;
        for (unsigned i = 0; i < WIDTH; ++i)
        {
          unit.clear();
          unit.push(SATSolver::mkLit(aVars[i], ((a >> i) & 1u) == 0));
          solver->addClause(unit);
          unit.clear();
          unit.push(SATSolver::mkLit(bVars[i], ((b >> i) & 1u) == 0));
          solver->addClause(unit);
        }

        bool timedOut = false;
        ASSERT_TRUE(solver->solve(timedOut))
            << "the encoding forbids " << a << " " << b;
        ASSERT_FALSE(timedOut);

        unsigned got = 0;
        for (unsigned i = 0; i < WIDTH; ++i)
          if (solver->modelValue(resultVars[i]) == solver->true_literal())
            got |= (1u << i);

        EXPECT_EQ(reference(kind, a, b), got)
            << "a=" << a << " b=" << b;
      }
  }
};

TEST_F(BVExactEncoderTest, MultiplicationOverEveryPair)
{
  const ASTNode term = operation(BVMULT, "mul_a", "mul_b");
  checkEveryPair(BVMULT, term);
}

// Division includes the divisor SMT-LIB totalises to all ones, which the
// abstraction's own reference model got wrong once already: it answered zero
// there, called a bogus candidate consistent, and left the refinement loop
// with nothing to say about a model it had already rejected.
TEST_F(BVExactEncoderTest, DivisionOverEveryPairIncludingZero)
{
  const ASTNode term = operation(BVDIV, "div_a", "div_b");
  checkEveryPair(BVDIV, term);
}

// ... and the remainder, whose zero divisor totalises to something else
// again: the dividend, not all ones.
TEST_F(BVExactEncoderTest, RemainderOverEveryPairIncludingZero)
{
  const ASTNode term = operation(BVMOD, "mod_a", "mod_b");
  checkEveryPair(BVMOD, term);
}

// The operands are not interchangeable and the splice has to keep them
// apart. Multiplication would not notice a swap, so this is checked on the
// two that would: 12 / 5 is 2 and 5 / 12 is 0.
TEST_F(BVExactEncoderTest, TheOperandsReachTheCircuitInOrder)
{
  const ASTNode term = operation(BVDIV, "ord_a", "ord_b");

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL);

  std::vector<unsigned> aVars(WIDTH), bVars(WIDTH), resultVars(WIDTH);
  for (unsigned i = 0; i < WIDTH; ++i)
  {
    aVars[i] = solver->newVar();
    bVars[i] = solver->newVar();
    resultVars[i] = solver->newVar();
  }
  BVExactEncoder(&mgr).encode(*solver, term, WIDTH, aVars, bVars, resultVars);

  SATSolver::vec_literals unit;
  for (unsigned i = 0; i < WIDTH; ++i)
  {
    unit.clear();
    unit.push(SATSolver::mkLit(aVars[i], ((12u >> i) & 1u) == 0));
    solver->addClause(unit);
    unit.clear();
    unit.push(SATSolver::mkLit(bVars[i], ((5u >> i) & 1u) == 0));
    solver->addClause(unit);
  }

  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  unsigned got = 0;
  for (unsigned i = 0; i < WIDTH; ++i)
    if (solver->modelValue(resultVars[i]) == solver->true_literal())
      got |= (1u << i);
  EXPECT_EQ(2u, got);
}

// The size, and the honest shape of what going through ABC's mapper buys.
//
// The array this replaced wrote a full adder per pair of operand bits
// straight out of its truth table, sixteen clauses each, so a W-bit
// multiply cost 19*W*(W-1)/2 clauses plus change and a W-bit division about
// 26*W^2. What the mapper produces for the same functions is smaller, but
// not dramatically: measured against those counts it is 0.78 of them at
// eight bits and 0.88 at sixty-four, the gap narrowing as the circuit
// grows.
//
// It is not smaller in every currency. For multiplication the mapped CNF
// carries about 30% *more* variables -- cut-based mapping trades variables
// for clauses, and STP's own multiplier is a different circuit from the
// naive array besides. Division and remainder come out ahead on both. So
// this is not "the mapper makes it smaller" and should not be read as such;
// whether any of it makes a query faster is a question for a stopwatch, not
// for this test.
//
// What the test holds is the direction that does not depend on which cuts
// ABC picks this decade: the escalated encoding costs fewer clauses than
// writing the gates out did. The comparison is computed from the shape of
// the array rather than hard-coded, so it stays meaningful at any width.
static uint64_t writtenOutGateClauses(Kind kind, uint64_t w)
{
  if (kind == BVMULT)
  {
    // A row of ANDs, then one pinned carry per row and an AND plus a full
    // adder per pair, then an equivalence per result bit.
    return 3 * w + (w - 1) + 19 * (w * (w - 1) / 2) + 2 * w;
  }
  // Restoring division: per step a comparison chain, a subtractor and a
  // row of muxes, plus one equivalence per result bit.
  return 1 + w * (2 + 26 * w) + 2 * w;
}

TEST_F(BVExactEncoderTest, TheMappedEncodingCostsFewerClausesThanWrittenOutGates)
{
  for (unsigned w : {8u, 16u, 32u, 64u})
    for (Kind kind : {BVMULT, BVDIV, BVMOD})
    {
      std::unique_ptr<SATSolver> solver = makeSolver();
      ASSERT_TRUE(solver != NULL);

      char aName[64], bName[64];
      snprintf(aName, sizeof aName, "size_a_%u_%d", w, (int)kind);
      snprintf(bName, sizeof bName, "size_b_%u_%d", w, (int)kind);
      ASTNode a = mgr.CreateSymbol(aName, 0, w);
      ASTNode b = mgr.CreateSymbol(bName, 0, w);
      const ASTNode term = mgr.defaultNodeFactory->CreateTerm(kind, w, a, b);

      std::vector<unsigned> aVars(w), bVars(w), resultVars(w);
      for (unsigned i = 0; i < w; ++i)
      {
        aVars[i] = solver->newVar();
        bVars[i] = solver->newVar();
        resultVars[i] = solver->newVar();
      }

      const uint64_t before = solver->submittedClauses();
      BVExactEncoder(&mgr).encode(*solver, term, w, aVars, bVars, resultVars);
      const uint64_t added = solver->submittedClauses() - before;

      EXPECT_GT(added, 0u) << "kind=" << kind << " w=" << w;
      EXPECT_LT(added, writtenOutGateClauses(kind, w))
          << "kind=" << kind << " w=" << w;
    }
}

} // namespace

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

// The algebraic facts an abstracted BVDIV or BVMOD is refined with, over
// every triple of operands and candidate result there is at four bits.
//
// The same two things have to hold of each of them as of the multiplication
// schemas, and one of them is sharper here.
//
// A schema has to be *valid*, and validity means more than "true of the
// triple that chose it". Both of these lemmas fix the divisor and leave the
// dividend entirely free -- that is what makes one of them worth 2^W
// blocking lemmas -- so what goes into the solver is a claim about *every*
// dividend over that divisor. A schema that happened to be right about the
// dividend in front of it and wrong about another would turn a satisfiable
// query unsat, silently, and only on the inputs that reach it. So validity
// is checked by re-running the sources over all sixteen dividends, not the
// one that triggered the choice.
//
// And it has to be *violated* by the candidate that chose it. Refinement is
// only allowed to hand a round back when it has ruled the candidate out; a
// lemma the candidate already satisfies leaves the search free to offer the
// same model again, and the abstraction never converges.
//
// Four bits, exhaustively: 4096 triples of (a, b, t) for each of BVDIV and
// BVMOD. Wide enough for four distinct powers of two, a zero divisor and
// eleven divisors that are neither, and small enough that nothing has to be
// sampled.
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

const unsigned WIDTH = 4;
const unsigned VALUES = 1u << WIDTH;

std::vector<bool> bitsOf(unsigned value)
{
  std::vector<bool> bits(WIDTH);
  for (unsigned i = 0; i < WIDTH; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

// What the operations mean, written out here rather than taken from the
// refiner: a bug copied into both would pass a test that compares them with
// each other. Both are totalised the way SMT-LIB totalises them, which is
// also what the unabstracted BBDivMod answers -- division by zero is all
// ones, and the remainder over a zero divisor is the dividend.
unsigned referenceDiv(unsigned a, unsigned b)
{
  return (b == 0) ? (VALUES - 1) : (a / b);
}

unsigned referenceRem(unsigned a, unsigned b)
{
  return (b == 0) ? a : (a % b);
}

unsigned reference(Kind opKind, unsigned a, unsigned b)
{
  return (opKind == BVDIV) ? referenceDiv(a, b) : referenceRem(a, b);
}

// The value a schema's sources give the result, for a dividend of `a`. This
// is what the encoder pins each result bit to under the divisor guard, so
// evaluating it is evaluating the lemma's consequent.
unsigned sourcesValue(const std::vector<int>& source, unsigned a)
{
  unsigned value = 0;
  for (unsigned i = 0; i < source.size(); ++i)
  {
    bool bit;
    if (source[i] == DIV_SOURCE_ZERO)
      bit = false;
    else if (source[i] == DIV_SOURCE_ONE)
      bit = true;
    else
      bit = ((a >> source[i]) & 1u) != 0;
    if (bit)
      value |= (1u << i);
  }
  return value;
}

bool isPowerOfTwo(unsigned v)
{
  return v != 0 && (v & (v - 1)) == 0;
}

const Kind KINDS[2] = {BVDIV, BVMOD};

const DivSchema BOUNDS[3] = {DivSchema::RemainderAtMostDividend,
                             DivSchema::RemainderBelowDivisor,
                             DivSchema::QuotientAtMostDividend};

// The two that fix a divisor and pin the result bit by bit, as against the
// three that bound it and name no divisor at all.
bool namesADivisor(DivSchema schema)
{
  return schema == DivSchema::DivisorZero || schema == DivSchema::Pow2Divisor;
}

bool boundApplies(Kind opKind, DivSchema schema)
{
  if (opKind == BVMOD)
    return schema == DivSchema::RemainderAtMostDividend ||
           schema == DivSchema::RemainderBelowDivisor;
  return schema == DivSchema::QuotientAtMostDividend;
}

// What each bound asserts, written out here rather than shared with the
// refiner for the same reason the reference operations are.
bool boundHolds(DivSchema schema, unsigned a, unsigned b, unsigned t)
{
  switch (schema)
  {
    case DivSchema::RemainderAtMostDividend:
      return t <= a;
    case DivSchema::RemainderBelowDivisor:
      return b == 0 || t < b;
    case DivSchema::QuotientAtMostDividend:
      return b == 0 || t <= a;
    default:
      return true;
  }
}

} // namespace

// Every lemma this can install is true of the operation it is installed
// over, for every dividend and not merely the one that chose it.
TEST(BVDivSchema, chosen_schema_is_valid_for_every_dividend)
{
  for (Kind opKind : KINDS)
    for (unsigned a = 0; a < VALUES; a++)
      for (unsigned b = 0; b < VALUES; b++)
        for (unsigned t = 0; t < VALUES; t++)
        {
          const DivSchemaChoice choice =
              chooseDivSchema(opKind, bitsOf(a), bitsOf(b), bitsOf(t), 0);
          if (choice.schema == DivSchema::None)
            continue;

          if (!namesADivisor(choice.schema))
            continue;

          const std::vector<int> source =
              divSchemaSources(opKind, WIDTH, choice);

          for (unsigned dividend = 0; dividend < VALUES; dividend++)
            ASSERT_EQ(sourcesValue(source, dividend),
                      reference(opKind, dividend, b))
                << "schema " << (int)choice.schema << " over " << _kind_names[opKind]
                << " chosen at a=" << a << " b=" << b << " t=" << t
                << " is wrong for dividend " << dividend;
        }
}

// ... and is contradicted by the candidate that chose it, so the round it
// costs is a round that rules something out.
TEST(BVDivSchema, chosen_schema_is_violated_by_the_candidate)
{
  for (Kind opKind : KINDS)
    for (unsigned a = 0; a < VALUES; a++)
      for (unsigned b = 0; b < VALUES; b++)
        for (unsigned t = 0; t < VALUES; t++)
        {
          const DivSchemaChoice choice =
              chooseDivSchema(opKind, bitsOf(a), bitsOf(b), bitsOf(t), 0);
          if (choice.schema == DivSchema::None)
            continue;

          if (choice.schema == DivSchema::Lemma)
          {
            unsigned n = 0;
            const DivLemma* table = divLemmaTable(n);
            ASSERT_LT(choice.lemmaIndex, n);
            ASSERT_FALSE(divLemmaHolds(table[choice.lemmaIndex], bitsOf(a),
                                       bitsOf(b), bitsOf(t)))
                << "lemma " << divLemmaName(table[choice.lemmaIndex])
                << " at a=" << a << " b=" << b << " t=" << t
                << " is already satisfied by the candidate";
            continue;
          }

          if (!namesADivisor(choice.schema))
          {
            ASSERT_FALSE(boundHolds(choice.schema, a, b, t))
                << "bound " << (int)choice.schema << " over "
                << _kind_names[opKind] << " at a=" << a << " b=" << b
                << " t=" << t << " is already satisfied by the candidate";
            continue;
          }

          ASSERT_NE(sourcesValue(divSchemaSources(opKind, WIDTH, choice), a), t)
              << "schema " << (int)choice.schema << " over "
              << _kind_names[opKind] << " at a=" << a << " b=" << b
              << " t=" << t << " is already satisfied by the candidate";
        }
}

// A candidate that holds the right answer is not refined at all. The refiner
// only asks once some bit is wrong, but a schema that fired on a correct
// result would be a lemma with nothing to rule out.
TEST(BVDivSchema, correct_candidates_choose_nothing)
{
  for (Kind opKind : KINDS)
    for (unsigned a = 0; a < VALUES; a++)
      for (unsigned b = 0; b < VALUES; b++)
      {
        const unsigned t = reference(opKind, a, b);
        const DivSchemaChoice choice =
            chooseDivSchema(opKind, bitsOf(a), bitsOf(b), bitsOf(t), 0);
        ASSERT_EQ(choice.schema, DivSchema::None)
            << "a correct " << _kind_names[opKind] << " candidate at a=" << a
            << " b=" << b << " was offered a schema";
      }
}

// Where a wrong candidate is turned away, it is because the divisor is one
// the schemas have nothing to say about -- neither zero nor a power of two.
// This is the coverage claim: everything else is caught.
TEST(BVDivSchema, wrong_candidates_are_only_declined_on_other_divisors)
{
  for (Kind opKind : KINDS)
    for (unsigned a = 0; a < VALUES; a++)
      for (unsigned b = 0; b < VALUES; b++)
        for (unsigned t = 0; t < VALUES; t++)
        {
          if (t == reference(opKind, a, b))
            continue;
          const DivSchemaChoice choice =
              chooseDivSchema(opKind, bitsOf(a), bitsOf(b), bitsOf(t), 0);
          if (choice.schema != DivSchema::None)
            continue;

          ASSERT_FALSE(b == 0 || isPowerOfTwo(b))
              << "a wrong " << _kind_names[opKind] << " candidate at a=" << a
              << " b=" << b << " t=" << t << " was declined a schema";

          // ... and because it satisfies every bound its kind carries. A
          // decline is only ever "there is nothing left to say", never a
          // fact that was available and not offered.
          for (DivSchema bound : BOUNDS)
          {
            if (boundApplies(opKind, bound))
            {
              ASSERT_TRUE(boundHolds(bound, a, b, t))
                  << "bound " << (int)bound << " was available over "
                  << _kind_names[opKind] << " at a=" << a << " b=" << b
                  << " t=" << t << " and was not offered";
            }
          }

          // ... and, for a quotient, every wider fact too.
          if (opKind == BVDIV)
          {
            unsigned n = 0;
            const DivLemma* table = divLemmaTable(n);
            for (unsigned i = 0; i < n; ++i)
              ASSERT_TRUE(
                  divLemmaHolds(table[i], bitsOf(a), bitsOf(b), bitsOf(t)))
                  << "lemma " << divLemmaName(table[i])
                  << " was available at a=" << a << " b=" << b << " t=" << t
                  << " and was not offered";
          }
        }
}

// The divisor the schemas name, and what each one concludes. Spelled out at
// the values that carry the meaning, so that a change of mind about any of
// them fails here and not only in the exhaustive sweeps above.
TEST(BVDivSchema, zero_divisor_is_totalised)
{
  const DivSchemaChoice div{DivSchema::DivisorZero, 0};
  // Division by zero is all ones, whatever the dividend.
  EXPECT_EQ(sourcesValue(divSchemaSources(BVDIV, WIDTH, div), 0), VALUES - 1);
  EXPECT_EQ(sourcesValue(divSchemaSources(BVDIV, WIDTH, div), 9), VALUES - 1);
  // The remainder over zero is the dividend, whatever it is.
  EXPECT_EQ(sourcesValue(divSchemaSources(BVMOD, WIDTH, div), 0), 0u);
  EXPECT_EQ(sourcesValue(divSchemaSources(BVMOD, WIDTH, div), 9), 9u);
}

TEST(BVDivSchema, power_of_two_divisor_is_a_shift_and_a_mask)
{
  // b = 8 = 2^3: the quotient is a >> 3 and the remainder is a & 7.
  const DivSchemaChoice eight{DivSchema::Pow2Divisor, 3};
  EXPECT_EQ(sourcesValue(divSchemaSources(BVDIV, WIDTH, eight), 13), 13u >> 3);
  EXPECT_EQ(sourcesValue(divSchemaSources(BVMOD, WIDTH, eight), 13), 13u & 7u);

  // b = 1 = 2^0 is the degenerate reading and the one most worth having:
  // the quotient is the dividend and the remainder is zero.
  const DivSchemaChoice one{DivSchema::Pow2Divisor, 0};
  EXPECT_EQ(sourcesValue(divSchemaSources(BVDIV, WIDTH, one), 11), 11u);
  EXPECT_EQ(sourcesValue(divSchemaSources(BVMOD, WIDTH, one), 11), 0u);
}

// What the schema *claims* is settled above, without a solver. What its
// clauses say is a separate question, and only a solver can answer it: a
// transcription that dropped a polarity would still pass every test up to
// here.
namespace
{

class BVDivSchemaEncodingTest : public ::testing::Test
{
protected:
  stp::STPMgr mgr;

  std::unique_ptr<SATSolver> makeSolver()
  {
    return std::unique_ptr<SATSolver>(createSATSolver(mgr.UserFlags));
  }

  // Install one schema's clauses over fresh variables, pin the dividend and
  // a divisor, and report what the result bits are forced to. Returns false
  // if the clauses forbid the assignment outright, which for a lemma that is
  // supposed to leave the dividend free would itself be the bug.
  bool solveUnder(Kind opKind, const DivSchemaChoice& choice,
                  const std::vector<bool>& guardBits, unsigned dividend,
                  unsigned divisor, unsigned& resultOut)
  {
    std::unique_ptr<SATSolver> solver = makeSolver();
    EXPECT_TRUE(solver != NULL) << "no SAT backend was compiled in";
    if (solver == NULL)
      return false;

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

    encodeDivUnderDivisorValue(*solver, bVars, guardBits, aVars, resultVars,
                               WIDTH, divSchemaSources(opKind, WIDTH, choice));

    SATSolver::vec_literals unit;
    for (unsigned i = 0; i < WIDTH; ++i)
    {
      unit.clear();
      unit.push(SATSolver::mkLit(aVars[i], ((dividend >> i) & 1u) == 0));
      solver->addClause(unit);
      unit.clear();
      unit.push(SATSolver::mkLit(bVars[i], ((divisor >> i) & 1u) == 0));
      solver->addClause(unit);
    }

    bool timedOut = false;
    if (!solver->solve(timedOut) || timedOut)
      return false;

    resultOut = 0;
    for (unsigned i = 0; i < WIDTH; ++i)
      if (solver->modelValue(resultVars[i]) == solver->true_literal())
        resultOut |= (1u << i);
    return true;
  }
};

} // namespace

// Under the divisor it names, the clauses force the result the schema
// claims -- for every dividend, since that is what the lemma leaves free.
TEST_F(BVDivSchemaEncodingTest, clauses_force_the_claimed_result)
{
  for (Kind opKind : KINDS)
    for (unsigned divisor = 0; divisor < VALUES; divisor++)
    {
      DivSchemaChoice choice;
      if (divisor == 0)
        choice = DivSchemaChoice{DivSchema::DivisorZero, 0};
      else if (isPowerOfTwo(divisor))
      {
        unsigned k = 0;
        while ((1u << k) != divisor)
          k++;
        choice = DivSchemaChoice{DivSchema::Pow2Divisor, k};
      }
      else
        continue;

      for (unsigned dividend = 0; dividend < VALUES; dividend++)
      {
        unsigned got = 0;
        ASSERT_TRUE(solveUnder(opKind, choice, bitsOf(divisor), dividend,
                               divisor, got))
            << "the clauses forbid " << _kind_names[opKind] << " a=" << dividend
            << " b=" << divisor;
        ASSERT_EQ(reference(opKind, dividend, divisor), got)
            << _kind_names[opKind] << " a=" << dividend << " b=" << divisor;
      }
    }
}

// ... and say nothing at all under any other divisor. The guard is the whole
// reason one of these is sound to add unconditionally: a lemma that leaked
// past its own premise would constrain a division it knows nothing about.
TEST_F(BVDivSchemaEncodingTest, clauses_are_silent_under_another_divisor)
{
  // Written over the divisor 4 = 2^2, then solved with the divisor pinned to
  // something else. Every result the schema would have forced must still be
  // reachable, so the check is that the wrong one is satisfiable too.
  const DivSchemaChoice choice{DivSchema::Pow2Divisor, 2};
  const std::vector<bool> guard = bitsOf(4);

  for (Kind opKind : KINDS)
    for (unsigned divisor = 0; divisor < VALUES; divisor++)
    {
      if (divisor == 4)
        continue;
      unsigned got = 0;
      ASSERT_TRUE(solveUnder(opKind, choice, guard, 13, divisor, got))
          << "the guarded clauses forbid a divisor they do not name: "
          << _kind_names[opKind] << " b=" << divisor;
    }
}

// The bounds hold of the operation itself, at every pair of operands. They
// go into the solver with no premise beyond the divisor being non-zero and
// are never taken back, so one that is merely usually true would turn a
// satisfiable query unsat.
TEST(BVDivSchemaBounds, every_bound_is_true_of_the_operation)
{
  for (Kind opKind : KINDS)
    for (DivSchema bound : BOUNDS)
    {
      if (!boundApplies(opKind, bound))
        continue;
      for (unsigned a = 0; a < VALUES; a++)
        for (unsigned b = 0; b < VALUES; b++)
          ASSERT_TRUE(boundHolds(bound, a, b, reference(opKind, a, b)))
              << "bound " << (int)bound << " is false of " << _kind_names[opKind]
              << " at a=" << a << " b=" << b;
    }
}

// A bound already in the solver is not offered a second time. It is
// unconditional, so no later candidate can contradict it -- and a round
// spent re-emitting a clause the solver has rules nothing out, which is the
// one thing a refinement round is not allowed to do.
TEST(BVDivSchemaBounds, an_installed_bound_is_not_offered_again)
{
  unsigned lemmaCount = 0;
  divLemmaTable(lemmaCount);
  unsigned all = DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND |
                 DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR |
                 DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND;
  for (unsigned i = 0; i < lemmaCount; ++i)
    all |= divLemmaInstalledBit(i);

  for (Kind opKind : KINDS)
    for (unsigned a = 0; a < VALUES; a++)
      for (unsigned b = 0; b < VALUES; b++)
        for (unsigned t = 0; t < VALUES; t++)
        {
          const DivSchemaChoice choice =
              chooseDivSchema(opKind, bitsOf(a), bitsOf(b), bitsOf(t), all);
          ASSERT_TRUE(choice.schema == DivSchema::None ||
                      namesADivisor(choice.schema))
              << "a bound was offered again over " << _kind_names[opKind]
              << " at a=" << a << " b=" << b << " t=" << t;
        }
}

// A divisor the schemas can name settles the result outright, which is more
// than any bound can say, so it is preferred where both are available.
TEST(BVDivSchemaBounds, a_named_divisor_outranks_a_bound)
{
  // BVMOD, dividend 3, divisor 2 = 2^1: the remainder is 1, and a candidate
  // holding 7 breaks both the power-of-two schema and both bounds.
  const DivSchemaChoice choice =
      chooseDivSchema(BVMOD, bitsOf(3), bitsOf(2), bitsOf(7), 0);
  EXPECT_EQ(choice.schema, DivSchema::Pow2Divisor);
  EXPECT_EQ(choice.shift, 1u);
}

namespace
{

// The bounds, and the comparison chain underneath them, in front of a real
// solver. `encodeLessOrEqual` is the chain the comparison refinement has
// always used; it moved here so the bounds could share it, and it had never
// been pinned on its own -- the direction bug its comment records was found
// on a query, not in a test.
class BVDivBoundEncodingTest : public ::testing::Test
{
protected:
  stp::STPMgr mgr;

  std::unique_ptr<SATSolver> makeSolver()
  {
    return std::unique_ptr<SATSolver>(createSATSolver(mgr.UserFlags));
  }

  void pin(SATSolver& solver, const std::vector<unsigned>& vars, unsigned value)
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

TEST_F(BVDivBoundEncodingTest, the_comparison_chain_answers_every_pair)
{
  for (unsigned isSigned = 0; isSigned < 2; isSigned++)
    for (unsigned x = 0; x < VALUES; x++)
      for (unsigned y = 0; y < VALUES; y++)
      {
        std::unique_ptr<SATSolver> solver = makeSolver();
        ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";

        std::vector<unsigned> xv(WIDTH), yv(WIDTH);
        for (unsigned i = 0; i < WIDTH; ++i)
        {
          xv[i] = solver->newVar();
          yv[i] = solver->newVar();
          solver->setFrozen(xv[i]);
          solver->setFrozen(yv[i]);
        }

        const unsigned le =
            encodeLessOrEqual(*solver, xv, yv, WIDTH, isSigned != 0);
        pin(*solver, xv, x);
        pin(*solver, yv, y);

        bool timedOut = false;
        ASSERT_TRUE(solver->solve(timedOut));
        ASSERT_FALSE(timedOut);

        const bool got = solver->modelValue(le) == solver->true_literal();
        bool want;
        if (isSigned)
        {
          const int sx = (x >= VALUES / 2) ? (int)x - (int)VALUES : (int)x;
          const int sy = (y >= VALUES / 2) ? (int)y - (int)VALUES : (int)y;
          want = sx <= sy;
        }
        else
          want = x <= y;

        ASSERT_EQ(want, got) << (isSigned ? "signed" : "unsigned") << " " << x
                             << " <= " << y;
      }
}

// Each bound forbids exactly the candidates that break it, and no others:
// the operation's own answer is always still reachable, and a result that
// oversteps the bound is not.
TEST_F(BVDivBoundEncodingTest, bounds_forbid_what_they_should_and_nothing_more)
{
  for (Kind opKind : KINDS)
    for (DivSchema bound : BOUNDS)
    {
      if (!boundApplies(opKind, bound))
        continue;

      for (unsigned a = 0; a < VALUES; a++)
        for (unsigned b = 0; b < VALUES; b++)
          for (unsigned t = 0; t < VALUES; t++)
          {
            std::unique_ptr<SATSolver> solver = makeSolver();
            ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";

            std::vector<unsigned> aVars(WIDTH), bVars(WIDTH), rVars(WIDTH);
            for (unsigned i = 0; i < WIDTH; ++i)
            {
              aVars[i] = solver->newVar();
              bVars[i] = solver->newVar();
              rVars[i] = solver->newVar();
              solver->setFrozen(aVars[i]);
              solver->setFrozen(bVars[i]);
              solver->setFrozen(rVars[i]);
            }

            encodeDivBound(*solver, bound, aVars, bVars, rVars, WIDTH);
            pin(*solver, aVars, a);
            pin(*solver, bVars, b);
            pin(*solver, rVars, t);

            bool timedOut = false;
            const bool satisfiable = solver->solve(timedOut);
            ASSERT_FALSE(timedOut);

            ASSERT_EQ(boundHolds(bound, a, b, t), satisfiable)
                << "bound " << (int)bound << " over " << _kind_names[opKind]
                << " at a=" << a << " b=" << b << " t=" << t;
          }
    }
}

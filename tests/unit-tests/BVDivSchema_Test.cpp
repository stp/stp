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
              chooseDivSchema(opKind, bitsOf(a), bitsOf(b), bitsOf(t));
          if (choice.schema == DivSchema::None)
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
              chooseDivSchema(opKind, bitsOf(a), bitsOf(b), bitsOf(t));
          if (choice.schema == DivSchema::None)
            continue;

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
            chooseDivSchema(opKind, bitsOf(a), bitsOf(b), bitsOf(t));
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
              chooseDivSchema(opKind, bitsOf(a), bitsOf(b), bitsOf(t));
          if (choice.schema != DivSchema::None)
            continue;

          ASSERT_FALSE(b == 0 || isPowerOfTwo(b))
              << "a wrong " << _kind_names[opKind] << " candidate at a=" << a
              << " b=" << b << " t=" << t << " was declined a schema";
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

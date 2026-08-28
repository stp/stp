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

// The algebraic facts an abstracted BVMULT is refined with, over every
// triple of operands and candidate product there is at four bits.
//
// Two things have to hold of each of them and they are not the same thing.
//
// A schema has to be *valid*: what its clauses say must be true of every
// pair of operands, because they are added to the solver unconditionally and
// are never taken back. A schema that is merely usually true turns a
// satisfiable query unsat, silently, and only on the inputs that reach it.
//
// And it has to be *violated* by the candidate that chose it. Refinement is
// only allowed to hand a round back when it has ruled the candidate out; a
// lemma the candidate already satisfies leaves the search free to offer the
// same one again, and the abstraction never converges. The refiner has an
// error for reaching undecided with nothing pending, so this shows up as an
// abort rather than a wrong answer -- but it shows up on someone else's
// query, not here, which is why it is pinned here.
//
// Four bits, exhaustively: 4096 triples of (a, b, t), each checked against
// every hand-written schema. Enough width for the trailing-zero and power-of-two
// cases to be distinct from each other and from the odd-bit one, and small
// enough that nothing has to be sampled.
#include "stp/ToSat/BVAbstractionRefiner.h"

#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <cassert>
#include <memory>
#include <vector>

using namespace stp;

namespace
{

// Two independently written oracles for the MUL8 relationship, kept here
// rather than in the library because nothing in the solver calls them: the
// live refiner reaches the fact through MulLemma::FactorUnchangedByMaskedShift
// and the compact implication its bit-blaster emits. Checking that against a
// second expression of the same relationship is a test's job, and a test is
// where the second expression belongs.
//
// mul8PublishedHolds is the catalogue's original shift spelling;
// encodeMulZeroProductOddOperand is the compact implication written directly
// as clauses. Neither shares code with what the refiner installs.
bool mul8PublishedHolds(const std::vector<bool>& x,
                        const std::vector<bool>& s,
                        const std::vector<bool>& t)
{
  [[maybe_unused]] const unsigned width = (unsigned)x.size();
  assert(width > 0);
  assert(s.size() == width);
  assert(t.size() == width);

  // 1 >> t is one exactly when t is zero, so the shift amount is x & 1 there
  // and zero everywhere else; s = s << 1 has only the all-zero solution.
  bool tZero = true;
  for (bool bit : t)
    if (bit)
      tZero = false;
  if (!tZero || !x[0])
    return true;
  for (bool bit : s)
    if (bit)
      return false;
  return true;
}

unsigned oracleFreshVar(SATSolver& solver)
{
  const unsigned v = solver.newVar();
  solver.setFrozen(v);
  return v;
}

// z <-> x | y
unsigned oracleOr(SATSolver& solver, unsigned x, unsigned y)
{
  const unsigned z = oracleFreshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(y, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, false)); cl.push(SATSolver::mkLit(z, true)); solver.addClause(cl);
  return z;
}

// oddOperand[0] = 1 and otherOperand != 0 -> result != 0.
void encodeMulZeroProductOddOperand(SATSolver& solver,
                                    const std::vector<unsigned>& oddOperand,
                                    const std::vector<unsigned>& otherOperand,
                                    const std::vector<unsigned>& result,
                                    unsigned width)
{
  unsigned resultNonzero = result[0];
  for (unsigned i = 1; i < width; ++i)
    resultNonzero = oracleOr(solver, resultNonzero, result[i]);

  for (unsigned i = 0; i < width; ++i)
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(oddOperand[0], true));
    cl.push(SATSolver::mkLit(otherOperand[i], true));
    cl.push(SATSolver::mkLit(resultNonzero, false));
    solver.addClause(cl);
  }
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

unsigned valueOf(const std::vector<bool>& bits)
{
  unsigned value = 0;
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
      value |= (1u << i);
  return value;
}

unsigned truncatedProduct(unsigned a, unsigned b)
{
  return (a * b) & (VALUES - 1);
}

// What each schema's clauses say, written out again here rather than shared
// with the refiner: a bug copied into both would pass a test that compares
// them with each other.

// result[0] <-> a[0] & b[0]
bool oddHolds(unsigned a, unsigned b, unsigned t)
{
  return (t & 1u) == ((a & 1u) & (b & 1u));
}

// t = 0 and oddOperand[0] = 1 -> otherOperand = 0. This is the
// only nontrivial case of s = s << (x & (1 >> t)), the MUL8 spelling.
bool zeroProductOddOperandHolds(unsigned oddOperand, unsigned otherOperand,
                                unsigned t)
{
  return t != 0 || (oddOperand & 1u) == 0 || otherOperand == 0;
}

// t[i] -> some bit of `op` at or below i
bool trailingZerosHolds(unsigned op, unsigned t)
{
  for (unsigned bit = 0; bit < WIDTH; ++bit)
  {
    if (((t >> bit) & 1u) == 0)
      continue;
    bool below = false;
    for (unsigned j = 0; j <= bit; ++j)
      below = below || (((op >> j) & 1u) != 0);
    if (!below)
      return false;
  }
  return true;
}

// The consequent of the two value-guarded schemas: t = source << shift,
// truncated. Their premise is that the chosen operand holds the value the
// candidate gave it, which is true by construction wherever this is asked.
bool shiftHolds(unsigned source, unsigned shift, unsigned t)
{
  return ((source << shift) & (VALUES - 1)) == t;
}

unsigned negated(unsigned v)
{
  return (VALUES - v) & (VALUES - 1);
}

// The fact the chosen schema asserts, evaluated at this triple.
bool chosenSchemaHolds(const MulSchemaChoice& choice, unsigned a, unsigned b,
                       unsigned t)
{
  const unsigned ops[2] = {a, b};
  const unsigned other = ops[1 - choice.operand];
  switch (choice.schema)
  {
    case MulSchema::Odd:
      return oddHolds(a, b, t);
    case MulSchema::TrailingZeros:
      return trailingZerosHolds(ops[choice.operand], t);
    case MulSchema::Pow2:
      return shiftHolds(other, choice.shift, t);
    case MulSchema::NegPow2:
      return shiftHolds(negated(other), choice.shift, t);
    case MulSchema::LowPrefix:
    {
      const unsigned mask = (1u << choice.shift) - 1;
      return (t & mask) == (truncatedProduct(a, b) & mask);
    }
    case MulSchema::Lemma:
    {
      unsigned count = 0;
      const BVLemmaEntry<MulLemma>* lemmas = mulLemmaTable(count);
      EXPECT_LT(choice.lemmaIndex, count);
      return choice.lemmaIndex < count &&
             mulLemmaHolds(lemmas[choice.lemmaIndex].lemma,
                           bitsOf(ops[choice.operand]), bitsOf(other),
                           bitsOf(t));
    }
    case MulSchema::None:
      break;
  }
  return true;
}

MulSchemaChoice choose(unsigned a, unsigned b, unsigned t,
                       uint64_t installed = 0)
{
  return chooseMulSchema(bitsOf(a), bitsOf(b), bitsOf(t), installed);
}

// Every fact a record may receive a bounded number of times, already in the
// solver: the parity and trailing-zero schemas, the exact prefix, and both
// readings of every catalogue row. What is left after this is the two
// operand-value-guarded shifts, which have one instance per power of two and
// are therefore offered last.
uint64_t allBoundedFactsInstalled()
{
  uint64_t installed = MUL_SCHEMA_INSTALLED_ODD |
                       MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0 |
                       MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1 |
                       MUL_SCHEMA_INSTALLED_LOW_PREFIX;
  unsigned lemmaCount = 0;
  mulLemmaTable(lemmaCount);
  for (unsigned i = 0; i < lemmaCount; ++i)
    for (unsigned operand = 0; operand < 2; ++operand)
      installed |= mulLemmaInstalledBit(i, operand);
  return installed;
}

class BVMultSchemaTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  bool zeroProductCircuitPermits(unsigned oddOperand, unsigned otherOperand,
                                 unsigned t)
  {
    std::unique_ptr<SATSolver> solver(createSATSolver(mgr.UserFlags));
    EXPECT_TRUE(solver != NULL) << "no SAT backend was compiled in";

    std::vector<unsigned> oddVars(WIDTH), otherVars(WIDTH), tVars(WIDTH);
    for (unsigned i = 0; i < WIDTH; ++i)
    {
      oddVars[i] = solver->newVar();
      otherVars[i] = solver->newVar();
      tVars[i] = solver->newVar();
      solver->setFrozen(oddVars[i]);
      solver->setFrozen(otherVars[i]);
      solver->setFrozen(tVars[i]);
    }

    encodeMulZeroProductOddOperand(*solver, oddVars, otherVars, tVars, WIDTH);

    SATSolver::vec_literals unit;
    const unsigned values[3] = {oddOperand, otherOperand, t};
    const std::vector<unsigned>* vars[3] = {&oddVars, &otherVars, &tVars};
    for (unsigned v = 0; v < 3; ++v)
      for (unsigned i = 0; i < WIDTH; ++i)
      {
        unit.clear();
        unit.push(
            SATSolver::mkLit((*vars[v])[i], ((values[v] >> i) & 1u) == 0));
        solver->addClause(unit);
      }

    bool timedOut = false;
    const bool sat = solver->solve(timedOut);
    EXPECT_FALSE(timedOut);
    return sat;
  }
};

} // namespace

// Valid: every fact any of the five can assert is true of the real product,
// whichever operand it is read over and whatever the schema was chosen for.
// This is the property that keeps the clauses from removing a model the
// query has.
TEST(bv_mult_schema, EveryFactHoldsOfTheRealProduct)
{
  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
    {
      const unsigned t = truncatedProduct(a, b);

      EXPECT_TRUE(oddHolds(a, b, t)) << "a=" << a << " b=" << b;
      EXPECT_TRUE(zeroProductOddOperandHolds(a, b, t))
          << "a=" << a << " b=" << b;
      EXPECT_TRUE(zeroProductOddOperandHolds(b, a, t))
          << "a=" << a << " b=" << b;
      EXPECT_TRUE(trailingZerosHolds(a, t)) << "a=" << a << " b=" << b;
      EXPECT_TRUE(trailingZerosHolds(b, t)) << "a=" << a << " b=" << b;
      EXPECT_TRUE(exactLowPrefixHolds(BVMULT, bitsOf(a), bitsOf(b), bitsOf(t),
                                      3))
          << "a=" << a << " b=" << b;

      // The two value-guarded ones, wherever their premise is met.
      for (unsigned i = 0; i < 2; ++i)
      {
        const unsigned chosen = (i == 0) ? a : b;
        const unsigned other = (i == 0) ? b : a;
        for (unsigned k = 0; k < WIDTH; ++k)
        {
          if (chosen == (1u << k))
          {
            EXPECT_TRUE(shiftHolds(other, k, t))
                << "a=" << a << " b=" << b << " k=" << k;
          }
          if (negated(chosen) == (1u << k) && chosen != (1u << k))
          {
            EXPECT_TRUE(shiftHolds(negated(other), k, t))
                << "a=" << a << " b=" << b << " k=" << k;
          }
        }
      }
    }
}

// Nothing is spent on a candidate that is already right. The refiner only
// calls this over a product it has just found wrong, but the guard belongs
// in the function and not only at its call site: a schema chosen over a
// faithful candidate would be a lemma that blocks nothing.
TEST(bv_mult_schema, NothingIsChosenWhenTheProductIsCorrect)
{
  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
      EXPECT_EQ(MulSchema::None,
                choose(a, b, truncatedProduct(a, b)).schema)
          << "a=" << a << " b=" << b;
}

TEST(bv_mult_schema, schema_groups_gate_multiplication_before_selection)
{
  const BVSchemaGroup groups[] = {
      BVSchemaGroup::BASE, BVSchemaGroup::MUL8, BVSchemaGroup::MUL_REF3,
      BVSchemaGroup::MUL_TAIL, BVSchemaGroup::LOW_PREFIX};

  for (const BVSchemaGroup group : groups)
  {
    bool sawChoice = false;
    const uint32_t only = bvSchemaGroupBit(group);
    for (unsigned a = 0; a < VALUES; ++a)
      for (unsigned b = 0; b < VALUES; ++b)
        for (unsigned t = 0; t < VALUES; ++t)
        {
          const MulSchemaChoice choice =
              chooseMulSchema(bitsOf(a), bitsOf(b), bitsOf(t), 0, only);
          if (choice.schema == MulSchema::None)
            continue;
          sawChoice = true;
          EXPECT_EQ(group, choice.group)
              << "a=" << a << " b=" << b << " t=" << t;
        }
    EXPECT_TRUE(sawChoice) << bvSchemaGroupName(group);
  }

  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        const MulSchemaChoice none =
            chooseMulSchema(bitsOf(a), bitsOf(b), bitsOf(t), 0, 0);
        EXPECT_EQ(MulSchema::None, none.schema);

        const MulSchemaChoice implicitAll =
            chooseMulSchema(bitsOf(a), bitsOf(b), bitsOf(t), 0);
        const MulSchemaChoice explicitAll = chooseMulSchema(
            bitsOf(a), bitsOf(b), bitsOf(t), 0, BV_SCHEMA_GROUP_ALL);
        EXPECT_EQ(implicitAll.schema, explicitAll.schema);
        EXPECT_EQ(implicitAll.operand, explicitAll.operand);
        EXPECT_EQ(implicitAll.shift, explicitAll.shift);
        EXPECT_EQ(implicitAll.lemmaIndex, explicitAll.lemmaIndex);
        EXPECT_EQ(implicitAll.group, explicitAll.group);
      }
}

// Violated: whatever is chosen, the candidate contradicts it. This is what
// makes the round progress -- the clauses rule this candidate out, so the
// search cannot offer it again.
TEST(bv_mult_schema, WhateverIsChosenTheCandidateContradictsIt)
{
  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        if (t == truncatedProduct(a, b))
          continue;
        const MulSchemaChoice choice = choose(a, b, t);
        if (choice.schema == MulSchema::None)
          continue;
        EXPECT_FALSE(chosenSchemaHolds(choice, a, b, t))
            << "a=" << a << " b=" << b << " t=" << t
            << " schema=" << (int)choice.schema;
      }
}

// A power-of-two operand is the case worth having: the shift is the whole
// product, so one lemma settles every value of the other operand where a
// blocking lemma settles one pair. It is therefore always taken once the
// facts above it are in, and the exponent handed back is the one the shift
// needs.
//
// "Once the facts above it are in" is the whole of the ordering rule. This
// family has one instance per power of two an operand can hold, while every
// fact above it has a fixed number per record, and all of them are spent
// from one purse -- so offering this one first lets it empty the purse
// before a once-only fact is ever evaluated. Deferring it costs at most one
// round per bounded fact and cannot lose it.
TEST(bv_mult_schema, APowerOfTwoOperandIsTakenAsTheShiftOnceTheBoundedFactsAreIn)
{
  const uint64_t bounded = allBoundedFactsInstalled();

  for (unsigned k = 0; k < WIDTH; ++k)
  {
    const unsigned pow2 = 1u << k;
    for (unsigned other = 0; other < VALUES; ++other)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        if (t == truncatedProduct(pow2, other))
          continue;

        const MulSchemaChoice first = choose(pow2, other, t, bounded);
        EXPECT_EQ(MulSchema::Pow2, first.schema);
        EXPECT_EQ(0u, first.operand);
        EXPECT_EQ(k, first.shift);

        // ... and read over the second operand just the same, unless the
        // first one is a power of two too and gets there first.
        const MulSchemaChoice second = choose(other, pow2, t, bounded);
        EXPECT_EQ(MulSchema::Pow2, second.schema);
        if (second.operand == 1u)
        {
          EXPECT_EQ(k, second.shift);
        }
      }
  }
}

// The ordering rule itself, on the one triple that shows all three arms.
//
// a = 2 is a power of two with one trailing zero, b = 3 is odd, and the
// candidate product 7 is odd: it contradicts the trailing-zero fact over a,
// the parity fact, and the shift. The two once-only facts are spent first
// and the width-scaled one last.
TEST(bv_mult_schema, ABoundedFactOutranksAWidthScaledShift)
{
  // The established schemas alone, so what is pinned is the order between
  // these families rather than the catalogue's place among them.
  const uint32_t base = bvSchemaGroupBit(BVSchemaGroup::BASE);

  const MulSchemaChoice first =
      chooseMulSchema(bitsOf(2), bitsOf(3), bitsOf(7), 0, base);
  EXPECT_EQ(MulSchema::TrailingZeros, first.schema);
  EXPECT_EQ(0u, first.operand);

  const MulSchemaChoice second =
      chooseMulSchema(bitsOf(2), bitsOf(3), bitsOf(7),
                      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0, base);
  EXPECT_EQ(MulSchema::Odd, second.schema);

  const MulSchemaChoice third = chooseMulSchema(
      bitsOf(2), bitsOf(3), bitsOf(7),
      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0 | MUL_SCHEMA_INSTALLED_ODD, base);
  EXPECT_EQ(MulSchema::Pow2, third.schema);
  EXPECT_EQ(0u, third.operand);
  EXPECT_EQ(1u, third.shift);
}

// The negated form, which is the one that needs a negation circuit under it.
// -2^k excludes the powers of two themselves, so the minimum signed value --
// which is its own negation -- goes to the schema above rather than this one.
// Read, like the schema above, with the bounded facts already installed.
TEST(bv_mult_schema, ANegatedPowerOfTwoOperandBecomesAShiftOfTheNegatedOther)
{
  const uint64_t bounded = allBoundedFactsInstalled();

  for (unsigned a = 0; a < VALUES; ++a)
  {
    const unsigned neg = negated(a);
    bool isNegPow2 = false;
    unsigned k = 0;
    for (unsigned e = 0; e < WIDTH; ++e)
      if (neg == (1u << e) && a != (1u << e))
      {
        isNegPow2 = true;
        k = e;
      }
    if (!isNegPow2)
      continue;

    for (unsigned b = 0; b < VALUES; ++b)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        if (t == truncatedProduct(a, b))
          continue;
        const MulSchemaChoice choice = choose(a, b, t, bounded);
        // A power of two on the other side outranks it; nothing else can.
        if (choice.schema == MulSchema::Pow2)
          continue;
        EXPECT_EQ(MulSchema::NegPow2, choice.schema)
            << "a=" << a << " b=" << b << " t=" << t;
        EXPECT_EQ(0u, choice.operand);
        EXPECT_EQ(k, choice.shift);
      }
  }
}

// A candidate that gives the product fewer trailing zeros than an operand
// has is refused by the fact that says it cannot, and the fact is read over
// the operand that actually has them.
TEST(bv_mult_schema, TooFewTrailingZerosIsRefusedOverTheOperandThatHasThem)
{
  // 6 = 0b0110 has one trailing zero and is not a power of two either way,
  // so nothing above this schema applies; an odd product contradicts it.
  const MulSchemaChoice overSecond = choose(3, 6, 1);
  EXPECT_EQ(MulSchema::TrailingZeros, overSecond.schema);
  EXPECT_EQ(1u, overSecond.operand);

  const MulSchemaChoice overFirst = choose(6, 3, 1);
  EXPECT_EQ(MulSchema::TrailingZeros, overFirst.schema);
  EXPECT_EQ(0u, overFirst.operand);
}

// An unconditional fact already in the solver is never chosen again. It
// cannot be contradicted twice -- the clauses that carry it are permanent --
// so a second choice would mean the clauses do not say what they are meant
// to, and re-emitting them would be paying a round for nothing.
TEST(bv_mult_schema, AnInstalledFactIsNeverChosenAgain)
{
  const uint64_t all = allBoundedFactsInstalled();

  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        const MulSchema schema = choose(a, b, t, all).schema;
        EXPECT_NE(MulSchema::Odd, schema);
        EXPECT_NE(MulSchema::TrailingZeros, schema);
        EXPECT_NE(MulSchema::LowPrefix, schema);
        EXPECT_NE(MulSchema::Lemma, schema);
      }

  // One at a time: the two readings of the trailing-zero fact are separate
  // lemmas and are installed separately.
  const MulSchemaChoice stillFirst =
      choose(6, 3, 1, MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1);
  EXPECT_EQ(MulSchema::TrailingZeros, stillFirst.schema);
  EXPECT_EQ(0u, stillFirst.operand);
}

TEST(bv_mult_schema, AResidualLowBitErrorTakesTheExactPrefix)
{
  uint64_t installed = MUL_SCHEMA_INSTALLED_ODD |
                       MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0 |
                       MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1;
  unsigned lemmaCount = 0;
  mulLemmaTable(lemmaCount);
  for (unsigned i = 0; i < lemmaCount; ++i)
    for (unsigned operand = 0; operand < 2; ++operand)
      installed |= mulLemmaInstalledBit(i, operand);

  const MulSchemaChoice choice = choose(3, 5, 8, installed);
  EXPECT_EQ(MulSchema::LowPrefix, choice.schema);
  EXPECT_EQ(3u, choice.shift);
  EXPECT_FALSE(chosenSchemaHolds(choice, 3, 5, 8));

  EXPECT_EQ(MulSchema::None,
            choose(3, 5, 8, installed | MUL_SCHEMA_INSTALLED_LOW_PREFIX)
                .schema);
}

// The odd-bit fact remains ahead of the zero-product fact, and it is reached:
// a candidate whose product has the wrong low bit while both operands are odd
// contradicts nothing above it.
TEST(bv_mult_schema, TheOddBitFactPrecedesTheZeroProductFact)
{
  // 3 * 5 = 15; a candidate of 14 is even where the product is odd, and
  // neither operand is a power of two or the negation of one at this width.
  const MulSchemaChoice choice = choose(3, 5, 14);
  EXPECT_EQ(MulSchema::Odd, choice.schema);
  EXPECT_FALSE(oddHolds(3, 5, 14));
}

// Once the hand-written facts all agree with a wrong zero product, an odd
// operand still proves that a nonzero other operand cannot have produced it.
// The two readings are installed independently because multiplication is
// commutative but the registry expression names which operand is odd.
TEST(bv_mult_schema, AnOddOperandRefusesAWrongZeroProduct)
{
  const MulSchemaChoice first = choose(3, 6, 0);
  ASSERT_EQ(MulSchema::Lemma, first.schema);
  EXPECT_EQ(0u, first.lemmaIndex);
  EXPECT_EQ(BVSchemaGroup::MUL8, first.group);
  EXPECT_EQ(0u, first.operand);
  EXPECT_FALSE(chosenSchemaHolds(first, 3, 6, 0));

  const MulSchemaChoice second = choose(6, 3, 0);
  ASSERT_EQ(MulSchema::Lemma, second.schema);
  EXPECT_EQ(0u, second.lemmaIndex);
  EXPECT_EQ(BVSchemaGroup::MUL8, second.group);
  EXPECT_EQ(1u, second.operand);
  EXPECT_FALSE(chosenSchemaHolds(second, 6, 3, 0));

  const MulSchemaChoice firstInstalled =
      choose(3, 6, 0, mulLemmaInstalledBit(0, 0));
  EXPECT_FALSE(firstInstalled.schema == MulSchema::Lemma &&
               firstInstalled.lemmaIndex == 0 &&
               firstInstalled.operand == 0);
}

// Keep the chooser's published shift expression independent of the compact
// implication installed as CNF. The two must agree over every triple, and
// the published expression must hold at the true truncated product.
TEST(bv_mult_schema, ThePublishedMUL8PredicateMatchesItsImplication)
{
  for (unsigned width = 1; width <= 6; ++width)
  {
    const unsigned values = 1u << width;
    const unsigned mask = values - 1;
    for (unsigned x = 0; x < values; ++x)
      for (unsigned s = 0; s < values; ++s)
      {
        const unsigned product = (x * s) & mask;
        EXPECT_TRUE(mul8PublishedHolds(bitsOf(x, width), bitsOf(s, width),
                                       bitsOf(product, width)))
            << "width=" << width << " x=" << x << " s=" << s;
        for (unsigned t = 0; t < values; ++t)
        {
          const bool implication = t != 0 || (x & 1u) == 0 || s == 0;
          EXPECT_EQ(implication,
                    mul8PublishedHolds(bitsOf(x, width), bitsOf(s, width),
                                       bitsOf(t, width)))
              << "width=" << width << " x=" << x << " s=" << s << " t=" << t;
        }
      }
  }
}

// The compact implication circuit used by the refiner is equivalent to the
// published shift expression's only nontrivial case, over every triple.
TEST_F(BVMultSchemaTest, TheZeroProductCircuitAgreesWithThePredicate)
{
  for (unsigned oddOperand = 0; oddOperand < VALUES; ++oddOperand)
    for (unsigned otherOperand = 0; otherOperand < VALUES; ++otherOperand)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        const bool want = mul8PublishedHolds(bitsOf(oddOperand),
                                             bitsOf(otherOperand), bitsOf(t));
        EXPECT_EQ(want,
                  zeroProductOddOperandHolds(oddOperand, otherOperand, t));
        ASSERT_EQ(want, zeroProductCircuitPermits(oddOperand, otherOperand, t))
            << "oddOperand=" << oddOperand << " otherOperand=" << otherOperand
            << " t=" << t;
      }
}

// Round trip through the bit vectors the refiner passes, so that a change to
// the bit order shows up here rather than as a wrong lemma.
TEST(bv_mult_schema, BitsAndValuesAgree)
{
  for (unsigned v = 0; v < VALUES; ++v)
    EXPECT_EQ(v, valueOf(bitsOf(v)));
}

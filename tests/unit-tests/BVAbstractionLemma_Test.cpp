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

// One harness for every imported arithmetic registry. It checks four
// independent claims: each value predicate is a theorem of the operation,
// every declared width restriction is necessary, the circuit installed in the
// SAT solver accepts exactly the triples the predicate does, and the facts
// agree with the circuit STP blasts for the operation rather than only with
// the reference functions written here. The tables come from the refiner
// itself, so adding a fact without adding a test case is impossible.
//
// Exhaustive where it fits and sampled where it does not. Six bits is what an
// exhaustive pass over 2^(2W) operand pairs can afford; the abstraction does
// not run below sixty-four, so every claim above is also asked at widths up
// to there. A fact that is a theorem below seven bits and false at thirty-two
// installs a clause the query does not entail, which is the one failure that
// turns a satisfiable query unsatisfiable.
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/BVExactEncoder.h"

#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <functional>
#include <memory>
#include <set>
#include <string>
#include <vector>

using namespace stp;

namespace
{

const unsigned MAX_WIDTH = 6;
const unsigned CIRCUIT_WIDTHS[] = {3, 4};

// Widths the circuit and the predicate are compared at by sampling rather
// than exhaustively. Four bits is not a wide enough net on its own: the
// barrel shifters inside these circuits gain a stage at five bits and
// another at nine, and every adder and comparator in them widens with the
// operands, so a circuit that stopped agreeing with its predicate above four
// bits would go unnoticed. Exhaustive is out of reach up here -- twelve bits
// is 2^36 triples -- and unnecessary: what has to be exercised is the
// structure, and the structure repeats.
const unsigned SAMPLED_CIRCUIT_WIDTHS[] = {5, 9, 12, 16, 32, 64};
const unsigned SAMPLES_PER_FACT = 400;

// Widths the value predicates are checked at by sampling. MAX_WIDTH above is
// what an exhaustive pass can afford and is nowhere near where the
// abstraction runs: bv_abstraction_width defaults to 64, so a fact that is a
// theorem below seven bits and false at thirty-two would pass every
// exhaustive test in this file and install a non-theorem into a live solver,
// which is the one failure that turns sat into unsat.
const unsigned SAMPLED_PREDICATE_WIDTHS[] = {8, 16, 32, 53, 64};

// Widths the facts are checked against the circuit STP blasts for the
// operation, rather than against the reference functions above. Small,
// because each one costs a solve per operand pair.
const unsigned BLASTED_WIDTHS[] = {6, 10, 14, 18};
const unsigned BLASTED_PAIRS = 200;

std::vector<bool> bitsOf(uint64_t value, unsigned width)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1ull) != 0;
  return bits;
}

uint64_t maskOf(unsigned width)
{
  return width >= 64 ? ~0ull : ((1ull << width) - 1);
}

// The values a sampled comparison draws from.
//
// Uniformly random operands would prove very little: almost every fact here
// is an implication, and almost every random triple leaves the premise false
// and the fact vacuously true. Zero, one, the all-ones word, each power of
// two and its neighbours are what turn those premises on, so the pool is
// those first and random words after.
std::vector<uint64_t> samplePool(unsigned width, unsigned count)
{
  const uint64_t mask = maskOf(width);
  std::vector<uint64_t> pool;
  pool.push_back(0);
  pool.push_back(1);
  pool.push_back(2);
  pool.push_back(3);
  pool.push_back(mask);
  pool.push_back(mask - 1);
  for (unsigned k = 0; k < width; ++k)
  {
    const uint64_t bit = 1ull << k;
    pool.push_back(bit & mask);            // 2^k
    pool.push_back((bit - 1) & mask);      // the mask below it
    pool.push_back((bit + 1) & mask);
    pool.push_back((~bit) & mask);         // its complement
    pool.push_back(((~bit) + 1) & mask);   // -2^k
  }

  // A fixed generator, so a failure is reproducible and a green run is not
  // green by luck of the day.
  uint64_t state = 0x9e3779b97f4a7c15ull ^ (width * 2654435761ull);
  while (pool.size() < count)
  {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    uint64_t value = (state >> 11) & mask;
    // A third sparse and a third dense: a uniform word has about half its
    // bits set at every width, and the premises here turn on the other two
    // shapes.
    if (pool.size() % 3 == 1)
    {
      state = state * 6364136223846793005ull + 1442695040888963407ull;
      value &= (state >> 11) & mask;
    }
    else if (pool.size() % 3 == 2)
    {
      state = state * 6364136223846793005ull + 1442695040888963407ull;
      value |= (state >> 11) & mask;
    }
    pool.push_back(value);
  }
  return pool;
}

struct Fact
{
  std::string name;
  std::function<bool(unsigned)> applicable;
  std::function<bool(const std::vector<bool>&, const std::vector<bool>&,
                     const std::vector<bool>&)>
      holds;
  std::function<void(BVExactEncoder&, SATSolver&, unsigned,
                     const std::vector<unsigned>&, const std::vector<unsigned>&,
                     const std::vector<unsigned>&)>
      encode;
};

uint64_t referenceDiv(uint64_t x, uint64_t s, unsigned width)
{
  return s == 0 ? maskOf(width) : x / s;
}

uint64_t referenceRem(uint64_t x, uint64_t s, unsigned)
{
  return s == 0 ? x : x % s;
}

uint64_t referenceMul(uint64_t x, uint64_t s, unsigned width)
{
  // Truncating a 64-bit wraparound product to `width` bits is the same value
  // as truncating the exact one: every bit the wraparound lost is above 64
  // and so above the width.
  return (x * s) & maskOf(width);
}

uint64_t referenceAdd(uint64_t x, uint64_t s, unsigned width)
{
  return (x + s) & maskOf(width);
}

struct Family
{
  const char* name;
  unsigned expectedCount;
  uint64_t (*reference)(uint64_t, uint64_t, unsigned);
  std::vector<Fact> facts;
  // The operation itself, for the pass that checks these facts against the
  // circuit STP blasts rather than against `reference`.
  Kind opKind;
};

std::vector<Family> families()
{
  std::vector<Family> result;
  unsigned count = 0;

  Family div{"BVDIV", BV_DIV_LEMMA_COUNT, referenceDiv, {}, BVDIV};
  const BVLemmaEntry<DivLemma>* divTable = divLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const DivLemma lemma = divTable[i].lemma;
    div.facts.push_back(
        {divLemmaName(lemma),
         [lemma](unsigned width) { return divLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t)
         { return divLemmaHolds(lemma, x, s, t); },
         [lemma](BVExactEncoder& encoder, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& x, const std::vector<unsigned>& s,
                 const std::vector<unsigned>& t)
         { encoder.encodeDivLemma(solver, lemma, width, x, s, t); }});
  }
  result.push_back(div);

  Family rem{"BVMOD", BV_REM_LEMMA_COUNT, referenceRem, {}, BVMOD};
  const BVLemmaEntry<RemLemma>* remTable = remLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const RemLemma lemma = remTable[i].lemma;
    rem.facts.push_back(
        {remLemmaName(lemma),
         [lemma](unsigned width) { return remLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t)
         { return remLemmaHolds(lemma, x, s, t); },
         [lemma](BVExactEncoder& encoder, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& x, const std::vector<unsigned>& s,
                 const std::vector<unsigned>& t)
         { encoder.encodeRemLemma(solver, lemma, width, x, s, t); }});
  }
  result.push_back(rem);

  Family mul{"BVMULT", BV_MUL_LEMMA_COUNT, referenceMul, {}, BVMULT};
  const BVLemmaEntry<MulLemma>* mulTable = mulLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const MulLemma lemma = mulTable[i].lemma;
    mul.facts.push_back(
        {mulLemmaName(lemma),
         [lemma](unsigned width) { return mulLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t)
         { return mulLemmaHolds(lemma, x, s, t); },
         [lemma](BVExactEncoder& encoder, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& x, const std::vector<unsigned>& s,
                 const std::vector<unsigned>& t)
         { encoder.encodeMulLemma(solver, lemma, width, x, s, t); }});
  }
  result.push_back(mul);

  Family add{"BVPLUS", BV_ADD_LEMMA_COUNT, referenceAdd, {}, BVPLUS};
  const BVLemmaEntry<AddLemma>* addTable = addLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const AddLemma lemma = addTable[i].lemma;
    add.facts.push_back(
        {addLemmaName(lemma),
         [lemma](unsigned width) { return addLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t)
         { return addLemmaHolds(lemma, x, s, t); },
         [lemma](BVExactEncoder& encoder, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& x, const std::vector<unsigned>& s,
                 const std::vector<unsigned>& t)
         { encoder.encodeAddLemma(solver, lemma, width, x, s, t); }});
  }
  result.push_back(add);

  return result;
}

class BVAbstractionLemmaTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  struct Circuit
  {
    std::unique_ptr<SATSolver> solver;
    std::vector<unsigned> vars;
    unsigned width = 0;
  };

  Circuit build(const Fact& fact, unsigned width)
  {
    Circuit circuit;
    circuit.width = width;
    circuit.solver.reset(createSATSolver(mgr.UserFlags));
    EXPECT_TRUE(circuit.solver != NULL) << "no SAT backend was compiled in";
    EXPECT_TRUE(circuit.solver->supportsAssumptions());

    std::vector<unsigned> x(width), s(width), t(width);
    std::vector<unsigned>* groups[] = {&x, &s, &t};
    for (unsigned group = 0; group < 3; ++group)
      for (unsigned bit = 0; bit < width; ++bit)
      {
        (*groups[group])[bit] = circuit.solver->newVar();
        circuit.solver->setFrozen((*groups[group])[bit]);
      }

    BVExactEncoder encoder(&mgr);
    fact.encode(encoder, *circuit.solver, width, x, s, t);
    for (unsigned group = 0; group < 3; ++group)
      circuit.vars.insert(circuit.vars.end(), groups[group]->begin(),
                          groups[group]->end());
    return circuit;
  }

  bool permits(Circuit& circuit, uint64_t x, uint64_t s, uint64_t t)
  {
    SATSolver::vec_literals assumptions;
    const uint64_t values[] = {x, s, t};
    for (unsigned group = 0; group < 3; ++group)
      for (unsigned bit = 0; bit < circuit.width; ++bit)
        assumptions.push(
            SATSolver::mkLit(circuit.vars[group * circuit.width + bit],
                             ((values[group] >> bit) & 1ull) == 0));

    bool timedOut = false;
    const bool sat =
        circuit.solver->solveWithAssumptions(assumptions, timedOut);
    EXPECT_FALSE(timedOut);
    return sat;
  }

  // The operation as STP encodes it: the same BitBlaster entry point a plain
  // solve uses, mapped to CNF by the same ABC pass, over three vectors of
  // free variables. Addition has no exact entry point in BVExactEncoder --
  // the refinement defines an abstracted BVPLUS with the prefix encoder at
  // full width -- so that is the circuit used for it, which is also the one
  // the refiner installs.
  Circuit blastOperation(Kind opKind, unsigned width, unsigned tag)
  {
    Circuit circuit;
    circuit.width = width;
    circuit.solver.reset(createSATSolver(mgr.UserFlags));
    EXPECT_TRUE(circuit.solver != NULL) << "no SAT backend was compiled in";

    std::vector<unsigned> x(width), s(width), t(width);
    std::vector<unsigned>* groups[] = {&x, &s, &t};
    for (unsigned group = 0; group < 3; ++group)
      for (unsigned bit = 0; bit < width; ++bit)
      {
        (*groups[group])[bit] = circuit.solver->newVar();
        circuit.solver->setFrozen((*groups[group])[bit]);
      }

    if (opKind == BVPLUS)
      encodeAddLowPrefix(*circuit.solver, x, s, t, width, width);
    else
    {
      // Distinct symbol names per call: the manager is shared across the
      // widths this runs at, and one name cannot carry two widths.
      const std::string suffix =
          "_" + std::to_string(width) + "_" + std::to_string(tag);
      ASTNode a = mgr.CreateSymbol(("blast_a" + suffix).c_str(), 0, width);
      ASTNode b = mgr.CreateSymbol(("blast_b" + suffix).c_str(), 0, width);
      const ASTNode term =
          mgr.defaultNodeFactory->CreateTerm(opKind, width, a, b);
      BVExactEncoder encoder(&mgr);
      encoder.encode(*circuit.solver, term, width, x, s, t);
    }

    for (unsigned group = 0; group < 3; ++group)
      circuit.vars.insert(circuit.vars.end(), groups[group]->begin(),
                          groups[group]->end());
    return circuit;
  }

  // What that circuit says the result is for one operand pair. The operation
  // is a function, so the model's result bits are its only answer.
  uint64_t blastedResult(Circuit& circuit, uint64_t x, uint64_t s)
  {
    SATSolver::vec_literals assumptions;
    const uint64_t values[] = {x, s};
    for (unsigned group = 0; group < 2; ++group)
      for (unsigned bit = 0; bit < circuit.width; ++bit)
        assumptions.push(
            SATSolver::mkLit(circuit.vars[group * circuit.width + bit],
                             ((values[group] >> bit) & 1ull) == 0));

    bool timedOut = false;
    const bool sat =
        circuit.solver->solveWithAssumptions(assumptions, timedOut);
    EXPECT_FALSE(timedOut);
    EXPECT_TRUE(sat) << "the blasted operation refused an operand pair";
    if (!sat)
      return 0;

    uint64_t result = 0;
    for (unsigned bit = 0; bit < circuit.width; ++bit)
    {
      const unsigned var = circuit.vars[2 * circuit.width + bit];
      if (circuit.solver->modelValue(var) == circuit.solver->true_literal())
        result |= (uint64_t{1} << bit);
    }
    return result;
  }
};

} // namespace

TEST(BVAbstractionLemma, registries_have_complete_unique_metadata)
{
  for (const Family& family : families())
  {
    EXPECT_EQ(family.expectedCount, family.facts.size()) << family.name;
    std::set<std::string> names;
    for (const Fact& fact : family.facts)
    {
      EXPECT_FALSE(fact.name.empty()) << family.name;
      EXPECT_NE("unknown", fact.name) << family.name;
      EXPECT_TRUE(names.insert(fact.name).second)
          << family.name << " has duplicate name " << fact.name;
    }
  }
}

TEST(BVAbstractionLemma, custom_facts_have_the_ranked_registry_positions)
{
  unsigned count = 0;
  const BVLemmaEntry<DivLemma>* div = divLemmaTable(count);
  ASSERT_EQ(BV_DIV_LEMMA_COUNT, count);
  EXPECT_EQ(DivLemma::QuotientIsOne, div[3].lemma);

  const BVLemmaEntry<RemLemma>* rem = remLemmaTable(count);
  ASSERT_EQ(BV_REM_LEMMA_COUNT, count);
  EXPECT_EQ(RemLemma::RemainderIsDifference, rem[3].lemma);

  const BVLemmaEntry<MulLemma>* mul = mulLemmaTable(count);
  ASSERT_EQ(BV_MUL_LEMMA_COUNT, count);
  EXPECT_EQ(MulLemma::FactorUnchangedByMaskedShift, mul[0].lemma);
  EXPECT_EQ(MulLemma::FactorAndProductNotOr, mul[1].lemma);
}

TEST(BVAbstractionLemma, every_enumerator_and_its_diagnostic_name_agree)
{
  struct DivName
  {
    DivLemma lemma;
    const char* name;
  };
  const DivName divNames[] = {
      {DivLemma::DivisorOrQuotientNotMaskedDividend, "divisor-or-quotient-not-masked-dividend"},
      {DivLemma::DivisorOrOneNotDividendWithoutQuotient, "divisor-or-one-not-dividend-without-quotient"},
      {DivLemma::DivisorNotNegatedSelfShiftedByHalfQuotient,
       "divisor-not-negated-self-shifted-by-half-quotient"},
      {DivLemma::DividendNotNegatedAndDoubledQuotient, "dividend-not-negated-and-doubled-quotient"},
      {DivLemma::QuotientAboveDoubledDividendShiftedByDivisor,
       "quotient-above-doubled-dividend-shifted-by-divisor"},
      {DivLemma::DividendAboveDivisorShiftedByNegatedOr,
       "dividend-above-divisor-shifted-by-negated-or"},
      {DivLemma::DividendAboveQuotientShiftedByNegatedOr,
       "dividend-above-quotient-shifted-by-negated-or"},
      {DivLemma::DividendAboveDivisorShiftedByNegatedXor,
       "dividend-above-divisor-shifted-by-negated-xor"},
      {DivLemma::DividendAboveQuotientShiftedByNegatedXor,
       "dividend-above-quotient-shifted-by-negated-xor"},
      {DivLemma::DividendNotQuotientPlusDivisorOrSum, "dividend-not-quotient-plus-divisor-or-sum"},
      {DivLemma::DividendNotQuotientPlusOnePlusShiftedOne,
       "dividend-not-quotient-plus-one-plus-shifted-one"},
      {DivLemma::DivisorAboveSumShiftedByQuotient, "divisor-above-sum-shifted-by-quotient"},
      {DivLemma::DivisorXorOrAboveQuotientXorOne, "divisor-xor-or-above-quotient-xor-one"},
      {DivLemma::QuotientAboveDividendShiftedByDivisorLessOne,
       "quotient-above-dividend-shifted-by-divisor-less-one"},
      {DivLemma::DividendNotOneLessShiftedDividend, "dividend-not-one-less-shifted-dividend"}};
  for (const DivName& item : divNames)
    EXPECT_STREQ(item.name, divLemmaName(item.lemma));

  struct MulName
  {
    MulLemma lemma;
    const char* name;
  };
  const MulName mulNames[] = {
      {MulLemma::FactorNotNegatedProductOrLowBit, "factor-not-negated-product-or-low-bit"},
      {MulLemma::ProductNotOddFactorShiftedByShiftedProduct,
       "product-not-odd-factor-shifted-by-shifted-product"},
      {MulLemma::ProductAboveMaskedShiftedFactors, "product-above-masked-shifted-factors"},
      {MulLemma::FactorNotOneXorFactorShiftedByXor, "factor-not-one-xor-factor-shifted-by-xor"},
      {MulLemma::ProductNotOneOrNegatedXor, "product-not-one-or-negated-xor"},
      {MulLemma::ProductNotHighOnesOrXor, "product-not-high-ones-or-xor"},
      {MulLemma::FactorNotShiftedFactorLessOne, "factor-not-shifted-factor-less-one"},
      {MulLemma::FactorNotOneLessShiftedFactor, "factor-not-one-less-shifted-factor"},
      {MulLemma::FactorNotOnePlusShiftedFactor, "factor-not-one-plus-shifted-factor"},
      {MulLemma::FactorNotOneLessShiftedFactorReversed,
       "factor-not-one-less-shifted-factor-reversed"},
      {MulLemma::FactorNotOnePlusShiftedFactorReversed,
       "factor-not-one-plus-shifted-factor-reversed"},
      {MulLemma::ProductNotOneOrSum, "product-not-one-or-sum"},
      {MulLemma::FactorNotNegatedShiftedFactor, "factor-not-negated-shifted-factor"}};
  for (const MulName& item : mulNames)
    EXPECT_STREQ(item.name, mulLemmaName(item.lemma));
}

TEST(BVAbstractionLemma, every_fact_is_true_of_its_operation)
{
  for (const Family& family : families())
    for (const Fact& fact : family.facts)
      for (unsigned width = 1; width <= MAX_WIDTH; ++width)
      {
        if (!fact.applicable(width))
          continue;
        const unsigned values = 1u << width;
        for (unsigned x = 0; x < values; ++x)
          for (unsigned s = 0; s < values; ++s)
          {
            const unsigned t = family.reference(x, s, width);
            ASSERT_TRUE(fact.holds(bitsOf(x, width), bitsOf(s, width),
                                   bitsOf(t, width)))
                << family.name << " " << fact.name << " at width " << width
                << ", x=" << x << " s=" << s << " result=" << t;
          }
      }
}

// The same question at the widths the abstraction is actually for.
//
// The exhaustive pass above stops at six bits because 2^(2W) operand pairs
// per fact is all it can afford, and six bits is a long way below the sixty-
// four bv_abstraction_width defaults to. Nothing about a fact makes it a
// theorem at every width for free -- several of these were synthesised rather
// than derived, and three of them already carry a width restriction for
// exactly that reason -- so a fact that stopped holding at thirty-two would
// have installed a non-theorem clause into a live solver with nothing in the
// tree to notice.
//
// Sampled, from the same pool the circuit comparison draws from: the values
// the premises turn on before random words, because almost every fact here is
// an implication and a uniform random pair leaves most of them vacuous.
TEST(BVAbstractionLemma, every_fact_is_true_of_its_operation_when_sampled_wide)
{
  for (const unsigned width : SAMPLED_PREDICATE_WIDTHS)
  {
    const std::vector<uint64_t> pool = samplePool(width, SAMPLES_PER_FACT);
    for (const Family& family : families())
      for (const Fact& fact : family.facts)
      {
        if (!fact.applicable(width))
          continue;
        // Every first operand against a seventh of the pool, offset by the
        // first, so the pairs are spread over the whole of it rather than
        // over a prefix -- and so this stays a few seconds rather than the
        // minute the full cross product costs.
        for (size_t i = 0; i < pool.size(); ++i)
          for (size_t j = i % 7; j < pool.size(); j += 7)
          {
            const uint64_t x = pool[i];
            const uint64_t s = pool[j];
            const uint64_t t = family.reference(x, s, width);
            ASSERT_TRUE(fact.holds(bitsOf(x, width), bitsOf(s, width),
                                   bitsOf(t, width)))
                << family.name << " " << fact.name << " at width " << width
                << ", x=" << x << " s=" << s << " result=" << t;
          }
      }
  }
}

// The oracle every one of the facts above is measured against.
//
// A candidate is faithful exactly when its result agrees with what the
// operation really is at the operand values it holds, so bvOperationValue is
// what the whole refinement loop rests on -- and unlike a fact, nothing else
// in the tree checks it. It used to be a schoolbook multiplier and a restoring
// divider written beside the loop, and the divider answered zero for a
// division by zero where SMT-LIB says all ones, which made a bogus candidate
// look consistent and left the loop with nothing to say about a model it had
// already rejected. It is STP's own constant evaluator now, which the rest of
// the solver folds constants with.
//
// Checked against the same references the facts are, so this is the evaluator
// against an independently written one and not against itself. Exhaustive
// where the facts are exhaustive, including every zero divisor, which is the
// case that went wrong.
TEST(BVAbstractionLemma, the_candidate_oracle_is_the_operation)
{
  const struct
  {
    Kind kind;
    const char* name;
    uint64_t (*reference)(uint64_t, uint64_t, unsigned);
  } operations[] = {{BVMULT, "BVMULT", referenceMul},
                    {BVDIV, "BVDIV", referenceDiv},
                    {BVMOD, "BVMOD", referenceRem}};

  for (const auto& operation : operations)
    for (unsigned width = 1; width <= MAX_WIDTH; ++width)
    {
      const unsigned values = 1u << width;
      for (unsigned x = 0; x < values; ++x)
        for (unsigned s = 0; s < values; ++s)
        {
          const uint64_t want = operation.reference(x, s, width);
          ASSERT_EQ(bitsOf(want, width),
                    bvOperationValue(operation.kind, bitsOf(x, width),
                                     bitsOf(s, width)))
              << operation.name << " at width " << width << ", x=" << x
              << " s=" << s;
        }
    }
}

// ... and at the widths the abstraction is actually for, from the same pool
// the facts are sampled from. A wrong answer up here is the one that matters:
// bv_abstraction_width defaults to sixty-four, so six bits is not where the
// oracle is ever asked anything.
TEST(BVAbstractionLemma, the_candidate_oracle_is_the_operation_when_sampled_wide)
{
  const struct
  {
    Kind kind;
    const char* name;
    uint64_t (*reference)(uint64_t, uint64_t, unsigned);
  } operations[] = {{BVMULT, "BVMULT", referenceMul},
                    {BVDIV, "BVDIV", referenceDiv},
                    {BVMOD, "BVMOD", referenceRem}};

  for (const unsigned width : SAMPLED_PREDICATE_WIDTHS)
  {
    const std::vector<uint64_t> pool = samplePool(width, SAMPLES_PER_FACT);
    for (const auto& operation : operations)
      for (size_t i = 0; i < pool.size(); ++i)
        for (size_t j = i % 7; j < pool.size(); j += 7)
        {
          const uint64_t x = pool[i];
          const uint64_t s = pool[j];
          const uint64_t want = operation.reference(x, s, width);
          ASSERT_EQ(bitsOf(want, width),
                    bvOperationValue(operation.kind, bitsOf(x, width),
                                     bitsOf(s, width)))
              << operation.name << " at width " << width << ", x=" << x
              << " s=" << s;
        }
  }
}

// The symmetry flag says what the predicate does, in both directions.
//
// Multiplication and addition are commutative, so the chooser offers each
// catalogue row over both operands -- but most of these expressions are not
// syntactically symmetric, and the ones that are were being offered twice for
// nothing: evaluated, found to hold, and skipped, on every call, for the life
// of the record. Fifteen of the twenty-seven rows.
//
// Marking them is a claim about a predicate, so it is checked like one. A row
// marked symmetric must agree with itself over exchanged operands at every
// triple, or the chooser has dropped a reading that could have fired; a row
// left unmarked must disagree somewhere, or the mark is missing and the waste
// is still there. Exhaustive below seven bits and sampled to sixty-four, from
// the same pool the facts themselves are sampled from.
TEST(BVAbstractionLemma, every_symmetric_fact_is_marked_and_no_other)
{
  struct Reading
  {
    const char* family;
    const char* name;
    bool marked;
    unsigned minWidth;
    unsigned excludedWidth;
    std::function<bool(const std::vector<bool>&, const std::vector<bool>&,
                       const std::vector<bool>&)>
        holds;
  };

  std::vector<Reading> readings;
  unsigned count = 0;
  const BVLemmaEntry<MulLemma>* mul = mulLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const MulLemma lemma = mul[i].lemma;
    readings.push_back({"BVMULT", mul[i].name, mul[i].symmetric,
                        mul[i].minWidth, mul[i].excludedWidth,
                        [lemma](const std::vector<bool>& x,
                                const std::vector<bool>& s,
                                const std::vector<bool>& t) {
                          return mulLemmaHolds(lemma, x, s, t);
                        }});
  }
  const BVLemmaEntry<AddLemma>* add = addLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const AddLemma lemma = add[i].lemma;
    readings.push_back({"BVPLUS", add[i].name, add[i].symmetric,
                        add[i].minWidth, add[i].excludedWidth,
                        [lemma](const std::vector<bool>& x,
                                const std::vector<bool>& s,
                                const std::vector<bool>& t) {
                          return addLemmaHolds(lemma, x, s, t);
                        }});
  }

  // Five bits rather than six: this compares TRIPLES, so the exhaustive pass
  // is 2^(3W) per row where the fact checks above are 2^(2W), and the sixth
  // bit alone costs more than the rest of the file.
  const unsigned SWAP_MAX_WIDTH = 5;

  for (const Reading& reading : readings)
  {
    bool swapAgrees = true;
    for (unsigned width = 1; width <= SWAP_MAX_WIDTH; ++width)
    {
      if (width < reading.minWidth || width == reading.excludedWidth)
        continue;
      const unsigned values = 1u << width;
      for (unsigned x = 0; x < values; ++x)
        for (unsigned s = 0; s < values; ++s)
          for (unsigned t = 0; t < values; ++t)
          {
            const bool straight = reading.holds(
                bitsOf(x, width), bitsOf(s, width), bitsOf(t, width));
            const bool swapped = reading.holds(
                bitsOf(s, width), bitsOf(x, width), bitsOf(t, width));
            if (straight == swapped)
              continue;
            swapAgrees = false;
            ASSERT_FALSE(reading.marked)
                << reading.family << " " << reading.name
                << " is marked symmetric but disagrees at width " << width
                << ", x=" << x << " s=" << s << " result=" << t;
          }
    }

    EXPECT_EQ(reading.marked, swapAgrees)
        << reading.family << " " << reading.name
        << (reading.marked ? " is marked symmetric and is not"
                           : " is symmetric and is not marked");
  }

  // ... and at the widths the abstraction actually runs at, where a row that
  // agreed below seven bits could still part company.
  for (const unsigned width : SAMPLED_PREDICATE_WIDTHS)
  {
    const std::vector<uint64_t> pool = samplePool(width, SAMPLES_PER_FACT);
    for (const Reading& reading : readings)
    {
      if (!reading.marked || width < reading.minWidth ||
          width == reading.excludedWidth)
        continue;
      // One result per operand pair, drawn from the same pool: symmetry is a
      // statement about exchanging the operands, so sweeping the result as
      // well multiplies the work by the pool without asking anything new of
      // the claim.
      for (size_t i = 0; i < pool.size(); ++i)
        for (size_t j = i % 7; j < pool.size(); j += 7)
        {
          const std::vector<bool> t = bitsOf(pool[(i + j) % pool.size()], width);
          ASSERT_EQ(reading.holds(bitsOf(pool[i], width),
                                  bitsOf(pool[j], width), t),
                    reading.holds(bitsOf(pool[j], width),
                                  bitsOf(pool[i], width), t))
              << reading.family << " " << reading.name
              << " is marked symmetric but disagrees at width " << width
              << ", x=" << pool[i] << " s=" << pool[j];
        }
    }
  }
}

TEST(BVAbstractionLemma, every_refused_width_has_a_real_counterexample)
{
  for (const Family& family : families())
    for (const Fact& fact : family.facts)
      for (unsigned width = 1; width <= MAX_WIDTH; ++width)
      {
        if (fact.applicable(width))
          continue;
        const unsigned values = 1u << width;
        bool broken = false;
        for (unsigned x = 0; x < values && !broken; ++x)
          for (unsigned s = 0; s < values && !broken; ++s)
          {
            const unsigned t = family.reference(x, s, width);
            broken = !fact.holds(bitsOf(x, width), bitsOf(s, width),
                                 bitsOf(t, width));
          }
        EXPECT_TRUE(broken) << family.name << " " << fact.name
                            << " needlessly refuses width " << width;
      }
}

TEST(BVAbstractionLemma, every_fact_rules_out_a_candidate)
{
  const unsigned width = 4;
  const unsigned values = 1u << width;
  for (const Family& family : families())
    for (const Fact& fact : family.facts)
    {
      unsigned refuted = 0;
      for (unsigned x = 0; x < values; ++x)
        for (unsigned s = 0; s < values; ++s)
          for (unsigned t = 0; t < values; ++t)
            if (!fact.holds(bitsOf(x, width), bitsOf(s, width),
                            bitsOf(t, width)))
              ++refuted;
      EXPECT_GT(refuted, 0u)
          << family.name << " " << fact.name << " excludes no triple";
    }
}

// No fact may be another fact read the other way round.
//
// The chooser offers every commutative operation's facts in both operand
// readings, so a catalogue that also contains a fact's own mirror image holds
// an entry that can never be selected: by the time the chooser reaches it,
// both of its readings have already been offered as the original's. One such
// entry was imported before this was checked -- the low-bit implication for
// the second operand, which is the first operand's with x and s exchanged.
//
// A dead entry costs two installed-schema bits and two predicate evaluations
// per record per round, and reads as coverage it does not provide.
TEST(BVAbstractionLemma, no_fact_is_another_fact_with_its_operands_swapped)
{
  const unsigned width = 4;
  const unsigned values = 1u << width;
  for (const Family& family : families())
    for (size_t i = 0; i < family.facts.size(); ++i)
      for (size_t j = 0; j < family.facts.size(); ++j)
      {
        if (i == j) continue;
        if (!family.facts[i].applicable(width) ||
            !family.facts[j].applicable(width))
          continue;
        bool differs = false;
        for (unsigned x = 0; x < values && !differs; ++x)
          for (unsigned s = 0; s < values && !differs; ++s)
            for (unsigned t = 0; t < values && !differs; ++t)
              differs = family.facts[i].holds(bitsOf(x, width), bitsOf(s, width),
                                              bitsOf(t, width)) !=
                        family.facts[j].holds(bitsOf(s, width), bitsOf(x, width),
                                              bitsOf(t, width));
        EXPECT_TRUE(differs)
            << family.name << ": " << family.facts[j].name << " is "
            << family.facts[i].name << " with its operands exchanged, so the "
               "chooser can never select it";
      }
}

TEST_F(BVAbstractionLemmaTest, every_circuit_agrees_with_its_predicate_when_sampled_wide)
{
  for (const unsigned width : SAMPLED_CIRCUIT_WIDTHS)
  {
    const std::vector<uint64_t> pool = samplePool(width, SAMPLES_PER_FACT);
    for (const Family& family : families())
      for (const Fact& fact : family.facts)
      {
        if (!fact.applicable(width))
          continue;
        Circuit circuit = build(fact, width);
        for (unsigned i = 0; i < SAMPLES_PER_FACT; ++i)
        {
          // Rotate the three positions independently so the same value does
          // not sit in all three on every draw.
          const uint64_t x = pool[i % pool.size()];
          const uint64_t s = pool[(i * 7 + 3) % pool.size()];
          // Every third triple gets the operation's real answer, which is
          // where the implications with a determined conclusion live.
          const uint64_t t = (i % 3 == 0) ? family.reference(x, s, width)
                                          : pool[(i * 13 + 5) % pool.size()];
          const bool expected =
              fact.holds(bitsOf(x, width), bitsOf(s, width), bitsOf(t, width));
          ASSERT_EQ(expected, permits(circuit, x, s, t))
              << family.name << " " << fact.name << " at width " << width
              << ", x=" << x << " s=" << s << " t=" << t;
        }
      }
  }
}

TEST_F(BVAbstractionLemmaTest, every_circuit_matches_its_value_predicate)
{
  for (const unsigned width : CIRCUIT_WIDTHS)
  {
    const unsigned values = 1u << width;
    for (const Family& family : families())
      for (const Fact& fact : family.facts)
      {
        if (!fact.applicable(width))
          continue;
        Circuit circuit = build(fact, width);
        for (unsigned x = 0; x < values; ++x)
          for (unsigned s = 0; s < values; ++s)
            for (unsigned t = 0; t < values; ++t)
            {
              const bool expected = fact.holds(
                  bitsOf(x, width), bitsOf(s, width), bitsOf(t, width));
              ASSERT_EQ(expected, permits(circuit, x, s, t))
                  << family.name << " " << fact.name << " at width " << width
                  << ", x=" << x << " s=" << s << " t=" << t;
            }
      }
  }
}

// The facts, against the operation STP actually blasts.
//
// Everything above compares a fact with `referenceDiv` and its siblings --
// four functions written in this file. That leaves one thing unchecked, and
// it is the thing the wide lit fixtures in tests/query-files/
// bv-division-refinement were reaching for and cannot establish: those
// fixtures assert the negation of one fact and expect unsat, which is what
// installing the fact produces whether or not the fact is true. So there was
// no test anywhere that put a fact and STP's own arithmetic in the same room.
//
// Here the result is not computed, it is read out of a model of the circuit
// BBDivMod, BBMult and the prefix adder produce. That closes the loop three
// ways: the fact is checked against the operation the solver will actually be
// reasoning about, the reference functions above are checked against it too,
// and the SMT-LIB totalisations -- all ones for a zero divisor's quotient,
// the dividend for its remainder -- are taken from the blaster rather than
// asserted twice. The two have disagreed about exactly that before.
TEST_F(BVAbstractionLemmaTest, every_fact_is_true_of_the_bit_blasted_operation)
{
  unsigned tag = 0;
  for (const unsigned width : BLASTED_WIDTHS)
  {
    const std::vector<uint64_t> pool = samplePool(width, BLASTED_PAIRS);
    for (const Family& family : families())
    {
      Circuit circuit = blastOperation(family.opKind, width, tag++);
      for (unsigned i = 0; i < BLASTED_PAIRS; ++i)
      {
        const uint64_t x = pool[i % pool.size()];
        const uint64_t s = pool[(i * 7 + 3) % pool.size()];
        const uint64_t t = blastedResult(circuit, x, s);

        ASSERT_EQ(family.reference(x, s, width), t)
            << family.name << " at width " << width << ": the blasted "
            << "operation and this file's reference disagree, x=" << x
            << " s=" << s;

        for (const Fact& fact : family.facts)
        {
          if (!fact.applicable(width))
            continue;
          ASSERT_TRUE(fact.holds(bitsOf(x, width), bitsOf(s, width),
                                 bitsOf(t, width)))
              << family.name << " " << fact.name << " at width " << width
              << ", x=" << x << " s=" << s << " blasted result=" << t;
        }
      }
    }
  }
}

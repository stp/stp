/***********
AUTHORS: Andrew Teylu

BEGIN DATE: Aug, 2026

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

// The same harness BVAbstractionLemma_Test runs over the four registries,
// pointed at the schemas that are not registry rows.
//
// Those schemas are parameterised -- by a divisor value, an exponent, an
// operand reading, a prefix length -- so they cannot be table rows without a
// different signature per arm, and until now nothing reconciled what the
// chooser reads off a candidate with what the clauses it then installs say.
// That reconciliation is the whole reason the registry table exists, so the
// gap was in the safety net rather than in the code: an arm whose predicate
// and circuit drifted apart would either install a clause the candidate
// already satisfies -- the same model comes back and nothing converges -- or,
// the other way round, one the operation does not entail.
//
// So this asks the two questions the registry harness asks. Is each schema a
// theorem of its operation? And does the circuit the refiner installs accept
// exactly the triples the predicate the chooser used accepts?
//
// Both are asked of the shipped functions: `divSchemaHolds`/`mulSchemaHolds`/
// `exactLowPrefixHolds` are what the choosers call, and the circuits are the
// ones refineTerms installs.

#include "stp/ToSat/BVAbstractionRefiner.h"

#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <memory>
#include <cstring>
#include <set>
#include <string>
#include <vector>

using namespace stp;

namespace
{

// Exhaustive over every triple. Three and four bits is 512 and 4096 triples
// per schema, and four bits is where every parameterised arm still has more
// than one interesting exponent.
const unsigned EXHAUSTIVE_WIDTHS[] = {3, 4};

// Sampled, for the same reason BVAbstractionLemma_Test samples: the barrel
// shifters and comparators inside these circuits gain a stage at five bits
// and another at nine, and the widths the abstraction actually runs at start
// at sixty-four, where exhaustive is not a possibility.
const unsigned SAMPLED_WIDTHS[] = {5, 9, 12, 16, 32, 64};
const unsigned SAMPLES_PER_SCHEMA = 260;

typedef std::vector<bool> Bits;
typedef std::vector<unsigned> Vars;

Bits bitsOf(uint64_t value, unsigned width)
{
  Bits bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1ull) != 0;
  return bits;
}

uint64_t maskOf(unsigned width)
{
  return width >= 64 ? ~0ull : ((1ull << width) - 1);
}

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
  // as truncating the exact one.
  return (x * s) & maskOf(width);
}
uint64_t referenceAdd(uint64_t x, uint64_t s, unsigned width)
{
  return (x + s) & maskOf(width);
}

// One arm at one parameterisation: the claim, the circuit, and the operation
// the claim is about.
struct Schema
{
  std::string name;
  uint64_t (*reference)(uint64_t, uint64_t, unsigned);
  // Which raw operand the circuit reads negated, or -1 for neither.
  //
  // An abstracted subtraction is recorded as an addition over the operand
  // underneath the BVUMINUS, so the refiner hands the circuit the raw
  // variables and tells it which side arrived negated, while it hands the
  // predicate the semantic values -- `refineTerms` negates them before
  // calling the chooser. Asking the two the same question here means doing
  // the same thing.
  int negatedOperand = -1;
  std::function<bool(const Bits&, const Bits&, const Bits&)> holds;
  std::function<void(SATSolver&, unsigned, const Vars&, const Vars&,
                     const Vars&)>
      encode;
};

// The operand values the predicate is entitled to, given the raw ones the
// circuit is written over.
void semanticOperands(const Schema& schema, unsigned width, uint64_t& x,
                      uint64_t& s)
{
  const uint64_t mask = maskOf(width);
  if (schema.negatedOperand == 0)
    x = (0 - x) & mask;
  else if (schema.negatedOperand == 1)
    s = (0 - s) & mask;
}

// The exponents a parameterised arm is instantiated at. All of them where the
// width is small enough to afford it, and the boundaries plus the middle
// where it is not -- one, the two either side of the halfway point, and the
// top, which is where a shifter's last stage and a comparator's sign bit are.
std::vector<unsigned> exponents(unsigned width, unsigned lowest)
{
  std::vector<unsigned> out;
  if (width <= 12)
  {
    for (unsigned k = lowest; k < width; ++k)
      out.push_back(k);
    return out;
  }
  const unsigned candidates[] = {lowest,        lowest + 1,   width / 2 - 1,
                                 width / 2,     width / 2 + 1, width - 2,
                                 width - 1};
  std::set<unsigned> seen;
  for (unsigned k : candidates)
    if (k >= lowest && k < width && seen.insert(k).second)
      out.push_back(k);
  return out;
}

std::vector<Schema> schemas(unsigned width)
{
  std::vector<Schema> out;

  const auto divArm = [&](Kind opKind, DivSchema schema, unsigned shift,
                          const std::string& name) {
    Schema s;
    s.name = name;
    s.reference = (opKind == BVDIV) ? referenceDiv : referenceRem;
    s.holds = [opKind, schema, shift](const Bits& a, const Bits& b,
                                      const Bits& t)
    { return divSchemaHolds(opKind, schema, shift, a, b, t); };
    switch (schema)
    {
      case DivSchema::DivisorZero:
      case DivSchema::Pow2Divisor:
      {
        // The guard is a divisor value, so the circuit needs the bits of it.
        Bits guard(width, false);
        if (schema == DivSchema::Pow2Divisor)
          guard[shift] = true;
        DivSchemaChoice choice;
        choice.schema = schema;
        choice.shift = shift;
        const std::vector<int> source = divSchemaSources(opKind, width, choice);
        s.encode = [guard, source](SATSolver& solver, unsigned w, const Vars& a,
                                   const Vars& b, const Vars& t) {
          encodeDivUnderDivisorValue(solver, b, guard, a, t, w, source);
        };
        break;
      }
      case DivSchema::QuotientPow2Threshold:
        s.encode = [shift](SATSolver& solver, unsigned w, const Vars& a,
                           const Vars& b, const Vars& t)
        { encodeDivPow2Threshold(solver, a, b, t, w, shift); };
        break;
      case DivSchema::DivisorMagnitudeBound:
        s.encode = [shift](SATSolver& solver, unsigned w, const Vars& a,
                           const Vars& b, const Vars& t)
        { encodeDivisorMagnitudeBound(solver, a, b, t, w, shift); };
        break;
      default:
        s.encode = [schema](SATSolver& solver, unsigned w, const Vars& a,
                            const Vars& b, const Vars& t)
        { encodeDivBound(solver, schema, a, b, t, w); };
        break;
    }
    out.push_back(s);
  };

  divArm(BVDIV, DivSchema::DivisorZero, 0, "BVDIV zero-divisor");
  divArm(BVMOD, DivSchema::DivisorZero, 0, "BVMOD zero-divisor");
  for (unsigned k : exponents(width, 0))
  {
    divArm(BVDIV, DivSchema::Pow2Divisor, k,
           "BVDIV power-of-two-divisor 2^" + std::to_string(k));
    divArm(BVMOD, DivSchema::Pow2Divisor, k,
           "BVMOD power-of-two-divisor 2^" + std::to_string(k));
  }
  divArm(BVMOD, DivSchema::RemainderAtMostDividend, 0,
         "BVMOD remainder-at-most-dividend");
  divArm(BVMOD, DivSchema::RemainderBelowDivisor, 0,
         "BVMOD remainder-below-divisor");
  divArm(BVDIV, DivSchema::QuotientAtMostDividend, 0,
         "BVDIV quotient-at-most-dividend");
  for (unsigned k : exponents(width, 1))
  {
    divArm(BVDIV, DivSchema::QuotientPow2Threshold, k,
           "BVDIV power-of-two-quotient-threshold 2^" + std::to_string(k));
    divArm(BVDIV, DivSchema::DivisorMagnitudeBound, k,
           "BVDIV divisor-magnitude-bound 2^" + std::to_string(k));
  }

  const auto mulArm = [&](MulSchema schema, unsigned operand, unsigned shift,
                          const std::string& name) {
    Schema s;
    s.name = name;
    s.reference = referenceMul;
    s.holds = [schema, operand, shift](const Bits& a, const Bits& b,
                                       const Bits& t)
    { return mulSchemaHolds(schema, operand, shift, a, b, t); };
    switch (schema)
    {
      case MulSchema::Odd:
        s.encode = [](SATSolver& solver, unsigned, const Vars& a,
                      const Vars& b, const Vars& t)
        { encodeMulOdd(solver, a, b, t); };
        break;
      case MulSchema::TrailingZeros:
        s.encode = [operand](SATSolver& solver, unsigned w, const Vars& a,
                             const Vars& b, const Vars& t)
        { encodeMulTrailingZeros(solver, operand == 0 ? a : b, t, w); };
        break;
      case MulSchema::Pow2:
      case MulSchema::NegPow2:
      {
        // The refiner installs the negated-operand form over a vector it
        // minted with encodeNegate. Here the source is just the other
        // operand's own bits, negated by the same construction below.
        Bits guard(width, false);
        if (schema == MulSchema::Pow2)
          guard[shift] = true;
        else
        {
          // -2^shift, two's complement.
          for (unsigned i = shift; i < width; ++i)
            guard[i] = true;
        }
        const bool negateSource = (schema == MulSchema::NegPow2);
        s.encode = [guard, shift, operand, negateSource](
                       SATSolver& solver, unsigned w, const Vars& a,
                       const Vars& b, const Vars& t) {
          const Vars& fixed = operand == 0 ? a : b;
          const Vars& other = operand == 0 ? b : a;
          // The refiner installs the negated reading as encodeNegate composed
          // with the shift circuit, so the composition is what has to match
          // the predicate -- and it is the shipped encodeNegate, not a
          // rebuild of it, or the test would be checking itself.
          const Vars source =
              negateSource ? encodeNegate(solver, other, w) : other;
          encodeMulShiftUnderValue(solver, fixed, guard, source, t, w, shift);
        };
        break;
      }
      case MulSchema::LowPrefix:
        s.encode = [shift](SATSolver& solver, unsigned w, const Vars& a,
                           const Vars& b, const Vars& t)
        { encodeMulLowPrefix(solver, a, b, t, w, shift); };
        break;
      default:
        ADD_FAILURE() << "unhandled multiplication schema";
        break;
    }
    out.push_back(s);
  };

  mulArm(MulSchema::Odd, 0, 0, "BVMULT odd");
  for (unsigned operand = 0; operand < 2; ++operand)
  {
    mulArm(MulSchema::TrailingZeros, operand, 0,
           "BVMULT trailing-zeros operand " + std::to_string(operand));
    for (unsigned k : exponents(width, 0))
    {
      mulArm(MulSchema::Pow2, operand, k,
             "BVMULT power-of-two operand " + std::to_string(operand) + " 2^" +
                 std::to_string(k));
      mulArm(MulSchema::NegPow2, operand, k,
             "BVMULT negated-power-of-two operand " + std::to_string(operand) +
                 " 2^" + std::to_string(k));
    }
  }
  for (unsigned p = 1; p <= std::min(3u, width); ++p)
    mulArm(MulSchema::LowPrefix, 0, p,
           "BVMULT exact-low-prefix " + std::to_string(p));

  // The addition prefix, in every operand spelling the bit-blaster records.
  // At most one operand is ever negated, and the negated readings are the
  // ones nothing else covers.
  for (unsigned p = 1; p <= std::min(3u, width); ++p)
    for (unsigned negated = 0; negated < 3; ++negated)
    {
      const bool aNeg = negated == 1;
      const bool bNeg = negated == 2;
      Schema s;
      s.name = "BVPLUS exact-low-prefix " + std::to_string(p) +
               (aNeg ? " (first operand negated)"
                     : bNeg ? " (second operand negated)" : "");
      s.reference = referenceAdd;
      s.negatedOperand = aNeg ? 0 : bNeg ? 1 : -1;
      s.holds = [p](const Bits& a, const Bits& b, const Bits& t)
      { return exactLowPrefixHolds(BVPLUS, a, b, t, p); };
      s.encode = [p, aNeg, bNeg](SATSolver& solver, unsigned w, const Vars& a,
                                 const Vars& b, const Vars& t)
      { encodeAddLowPrefix(solver, a, b, t, w, p, aNeg, bNeg); };
      out.push_back(s);
    }

  return out;
}

// The values a sampled comparison draws from: what the guards turn on, then
// random words. Uniform operands would leave almost every guard false and
// almost every schema vacuously true.
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
    pool.push_back(bit & mask);
    pool.push_back((bit - 1) & mask);
    pool.push_back((bit + 1) & mask);
    pool.push_back((~bit) & mask);
    pool.push_back(((~bit) + 1) & mask); // -2^k
  }

  // A fixed generator, so a failure is reproducible.
  uint64_t state = 0x9e3779b97f4a7c15ull ^ (width * 0x2545f4914f6cdd1dull);
  while (pool.size() < count)
  {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    uint64_t v = (state >> 11) & mask;
    if (pool.size() % 3 == 1)
    {
      state = state * 6364136223846793005ull + 1442695040888963407ull;
      v &= (state >> 11) & mask;
    }
    else if (pool.size() % 3 == 2)
    {
      state = state * 6364136223846793005ull + 1442695040888963407ull;
      v |= (state >> 11) & mask;
    }
    pool.push_back(v);
  }
  return pool;
}

class BVSchemaCircuitTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  struct Circuit
  {
    std::unique_ptr<SATSolver> solver;
    Vars vars;
    unsigned width = 0;
  };

  Circuit build(const Schema& schema, unsigned width)
  {
    Circuit circuit;
    circuit.width = width;
    circuit.solver.reset(createSATSolver(mgr.UserFlags));
    EXPECT_TRUE(circuit.solver != NULL) << "no SAT backend was compiled in";
    EXPECT_TRUE(circuit.solver->supportsAssumptions());

    Vars x(width), s(width), t(width);
    Vars* groups[] = {&x, &s, &t};
    for (unsigned group = 0; group < 3; ++group)
      for (unsigned bit = 0; bit < width; ++bit)
      {
        (*groups[group])[bit] = circuit.solver->newVar();
        circuit.solver->setFrozen((*groups[group])[bit]);
      }

    schema.encode(*circuit.solver, width, x, s, t);
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
};

} // namespace

// Every schema has to be true of the operation it is about, or the refinement
// installs a clause the query does not entail and a satisfiable model is lost.
// The value-guarded arms carry their guard, so this asks the question over
// every divisor and operand rather than only the ones the chooser reaches
// them at.
TEST(BVSchemaCircuit, every_schema_is_true_of_its_operation)
{
  for (const unsigned width : EXHAUSTIVE_WIDTHS)
  {
    const uint64_t values = 1ull << width;
    for (const Schema& schema : schemas(width))
      for (uint64_t rawX = 0; rawX < values; ++rawX)
        for (uint64_t rawS = 0; rawS < values; ++rawS)
        {
          uint64_t x = rawX, s = rawS;
          semanticOperands(schema, width, x, s);
          const uint64_t t = schema.reference(x, s, width);
          ASSERT_TRUE(schema.holds(bitsOf(x, width), bitsOf(s, width),
                                   bitsOf(t, width)))
              << schema.name << " at width " << width << ", x=" << x
              << " s=" << s << " result=" << t;
        }
  }
}

TEST(BVSchemaCircuit, every_schema_is_true_of_its_operation_when_sampled_wide)
{
  for (const unsigned width : SAMPLED_WIDTHS)
  {
    const std::vector<uint64_t> pool = samplePool(width, SAMPLES_PER_SCHEMA);
    for (const Schema& schema : schemas(width))
      for (size_t i = 0; i < pool.size(); ++i)
        for (size_t j = 0; j < pool.size(); j += 7)
        {
          uint64_t x = pool[i], s = pool[j];
          semanticOperands(schema, width, x, s);
          const uint64_t t = schema.reference(x, s, width);
          ASSERT_TRUE(schema.holds(bitsOf(x, width), bitsOf(s, width),
                                   bitsOf(t, width)))
              << schema.name << " at width " << width << ", x=" << x
              << " s=" << s << " result=" << t;
        }
  }
}

// And the circuit has to accept exactly the triples the predicate accepts.
// Accepting fewer loses models; accepting more means the chooser can offer a
// schema whose clauses the candidate already satisfies, and the same model
// comes back for ever.
TEST_F(BVSchemaCircuitTest, every_schema_circuit_matches_its_predicate)
{
  for (const unsigned width : EXHAUSTIVE_WIDTHS)
  {
    const uint64_t values = 1ull << width;
    for (const Schema& schema : schemas(width))
    {
      Circuit circuit = build(schema, width);
      for (uint64_t x = 0; x < values; ++x)
        for (uint64_t s = 0; s < values; ++s)
          for (uint64_t t = 0; t < values; ++t)
          {
            // The predicate sees the semantic operands, the circuit the raw
            // ones -- the arrangement refineTerms uses.
            uint64_t semX = x, semS = s;
            semanticOperands(schema, width, semX, semS);
            const bool expected = schema.holds(
                bitsOf(semX, width), bitsOf(semS, width), bitsOf(t, width));
            ASSERT_EQ(expected, permits(circuit, x, s, t))
                << schema.name << " at width " << width << ", x=" << x
                << " s=" << s << " t=" << t;
          }
    }
  }
}

TEST_F(BVSchemaCircuitTest,
       every_schema_circuit_matches_its_predicate_when_sampled_wide)
{
  for (const unsigned width : SAMPLED_WIDTHS)
  {
    const std::vector<uint64_t> pool = samplePool(width, SAMPLES_PER_SCHEMA);
    for (const Schema& schema : schemas(width))
    {
      Circuit circuit = build(schema, width);
      for (unsigned i = 0; i < SAMPLES_PER_SCHEMA; ++i)
      {
        // Rotate the three positions independently, and give every third
        // triple the operation's real answer -- which is where the arms with
        // a determined conclusion actually say something.
        const uint64_t x = pool[i % pool.size()];
        const uint64_t s = pool[(i * 7 + 3) % pool.size()];
        uint64_t semX = x, semS = s;
        semanticOperands(schema, width, semX, semS);
        const uint64_t t = (i % 3 == 0)
                               ? schema.reference(semX, semS, width)
                               : pool[(i * 13 + 5) % pool.size()];
        const bool expected = schema.holds(
            bitsOf(semX, width), bitsOf(semS, width), bitsOf(t, width));
        ASSERT_EQ(expected, permits(circuit, x, s, t))
            << schema.name << " at width " << width << ", x=" << x
            << " s=" << s << " t=" << t;
      }
    }
  }
}

// Nothing else in the tree says how many of these there are, and the count is
// the only thing that would notice a new arm arriving without a row above.
TEST(BVSchemaCircuit, every_hand_written_schema_arm_is_covered)
{
  std::set<std::string> arms;
  for (const Schema& schema : schemas(8))
  {
    // Strip the parameterisation, leaving the arm.
    std::string name = schema.name;
    const size_t marker = name.find(" 2^");
    if (marker != std::string::npos)
      name = name.substr(0, marker);
    const size_t operand = name.find(" operand ");
    if (operand != std::string::npos)
      name = name.substr(0, operand);
    const size_t prefix = name.find("exact-low-prefix");
    if (prefix != std::string::npos)
      name = name.substr(0, prefix + strlen("exact-low-prefix"));
    arms.insert(name);
  }

  const char* expected[] = {"BVDIV zero-divisor",
                            "BVMOD zero-divisor",
                            "BVDIV power-of-two-divisor",
                            "BVMOD power-of-two-divisor",
                            "BVMOD remainder-at-most-dividend",
                            "BVMOD remainder-below-divisor",
                            "BVDIV quotient-at-most-dividend",
                            "BVDIV power-of-two-quotient-threshold",
                            "BVDIV divisor-magnitude-bound",
                            "BVMULT odd",
                            "BVMULT trailing-zeros",
                            "BVMULT power-of-two",
                            "BVMULT negated-power-of-two",
                            "BVMULT exact-low-prefix",
                            "BVPLUS exact-low-prefix"};
  for (const char* name : expected)
    EXPECT_EQ(1u, arms.count(name))
        << name << " is no longer covered by this harness";
  EXPECT_EQ(sizeof(expected) / sizeof(expected[0]), arms.size())
      << "a hand-written schema arm was added or removed without updating "
         "this harness";
}

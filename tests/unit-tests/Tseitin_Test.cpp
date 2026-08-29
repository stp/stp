/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

// The Tseitin writer over the in-house AIG.
//
// The central test needs no SAT solver, and is stronger than one would give.
// A Tseitin encoding claims two things: that every assignment the circuit
// admits satisfies the clauses, and that the clauses admit nothing else.  The
// first is checked directly.  The second is checked by unit propagation: this
// encoding is propagation-complete from the inputs -- fixing the CIs forces
// every other variable, by construction -- so BCP deriving exactly the
// simulated value for every variable says the clauses pin the circuit and
// nothing looser.  A solver would answer only "satisfiable", which a
// one-sided bug survives.

#include "stp/AIG/Tseitin.h"

#include <gtest/gtest.h>

#include <cstdint>
#include <cstdlib>
#include <random>
#include <sstream>
#include <vector>

using namespace stp;

namespace
{

// Node values under one assignment of the CIs.  Ascending is topological, so
// this is a single forward sweep -- the same property the writer's second
// pass leans on.
std::vector<uint8_t> simulate(const aig::Manager& m,
                              const std::vector<uint8_t>& ciValues)
{
  std::vector<uint8_t> value(m.nodeCount(), 0);
  unsigned seen = 0;
  for (aig::Node n = 1; n < m.nodeCount(); ++n)
  {
    if (m.isCi(n))
      value[n] = ciValues[seen++];
    else
    {
      const aig::Lit a = m.fanin0(n), b = m.fanin1(n);
      const uint8_t va = value[aig::nodeOf(a)] ^ (aig::isNeg(a) ? 1 : 0);
      const uint8_t vb = value[aig::nodeOf(b)] ^ (aig::isNeg(b) ? 1 : 0);
      value[n] = va & vb;
    }
  }
  return value;
}

uint8_t valueOf(const std::vector<uint8_t>& value, aig::Lit l)
{
  return value[aig::nodeOf(l)] ^ (aig::isNeg(l) ? 1 : 0);
}

// The writer's variable numbering, recomputed here rather than read out of
// the CNF, so that a change to the layout has to be made deliberately in two
// places instead of silently agreeing with itself.
struct Layout
{
  std::vector<uint32_t> nodeVar; // node -> variable, 0 for none
  std::vector<uint32_t> coVar;   // output -> variable, 0 when asserted
  uint32_t nVars = 1;
};

Layout layoutOf(const aig::Manager& m, const aig::Cone& cone)
{
  Layout l;
  l.nodeVar.assign(m.nodeCount(), 0);
  for (uint32_t i = 0; i < m.ciCount(); i++)
    l.nodeVar[m.ciNode(i)] = aig::Cone::ciVarBase() + i;

  l.coVar.assign(m.outputCount(), 0);
  for (uint32_t i = cone.firstNamedOutput(); i < m.outputCount(); i++)
    l.coVar[i] = cone.coVarBase() + (i - cone.firstNamedOutput());

  uint32_t next = cone.andVarBase();
  for (aig::Node n = 1; n < m.nodeCount(); ++n)
    if (m.isAnd(n) && cone.live(n))
      l.nodeVar[n] = next++;
  l.nVars = next;
  return l;
}

// What every variable is supposed to hold, given the CIs.  -1 for a variable
// the layout never handed out, which is only ever variable 0.
std::vector<int8_t> intendedValues(const aig::Manager& m,
                                   const aig::Cone& cone, const Layout& l,
                                   const std::vector<uint8_t>& value)
{
  std::vector<int8_t> want(l.nVars, -1);
  for (aig::Node n = 1; n < m.nodeCount(); ++n)
    if (l.nodeVar[n] != 0)
      want[l.nodeVar[n]] = static_cast<int8_t>(value[n]);
  for (uint32_t i = 0; i < m.outputCount(); i++)
    if (l.coVar[i] != 0)
      want[l.coVar[i]] = static_cast<int8_t>(valueOf(value, m.output(i)));
  (void)cone;
  return want;
}

bool clauseSatisfied(const CNF& cnf, uint64_t i, const std::vector<int8_t>& a)
{
  for (const int *p = cnf.clauseBegin(i), *stop = cnf.clauseEnd(i); p < stop;
       p++)
  {
    const uint32_t v = static_cast<uint32_t>(*p) >> 1;
    const int8_t want = (*p & 1) ? 0 : 1;
    if (a[v] == want)
      return true;
  }
  return false;
}

// Textbook BCP.  Quadratic and proud of it: the formulas here have tens of
// clauses, and a watched-literal scheme would be a second implementation to
// get wrong.  Returns false on a conflict.
bool propagate(const CNF& cnf, std::vector<int8_t>& a)
{
  bool changed = true;
  while (changed)
  {
    changed = false;
    for (uint64_t i = 0, n = cnf.clauseCount(); i < n; i++)
    {
      int unassigned = 0, lastLit = 0;
      bool sat = false;
      for (const int *p = cnf.clauseBegin(i), *stop = cnf.clauseEnd(i);
           p < stop; p++)
      {
        const uint32_t v = static_cast<uint32_t>(*p) >> 1;
        const int8_t want = (*p & 1) ? 0 : 1;
        if (a[v] < 0)
        {
          unassigned++;
          lastLit = *p;
        }
        else if (a[v] == want)
        {
          sat = true;
          break;
        }
      }
      if (sat)
        continue;
      if (unassigned == 0)
        return false;
      if (unassigned == 1)
      {
        a[static_cast<uint32_t>(lastLit) >> 1] = (lastLit & 1) ? 0 : 1;
        changed = true;
      }
    }
  }
  return true;
}

// A circuit with XORs and MUXes in it, since those are what the pattern
// matcher exists for and a pure-AND generator would never produce one.
void buildRandom(aig::Manager& m, std::mt19937& rng, unsigned nCi,
                 unsigned nGates, std::vector<aig::Lit>& pool)
{
  for (unsigned i = 0; i < nCi; i++)
    pool.push_back(m.createCi());

  for (unsigned g = 0; g < nGates; g++)
  {
    const auto pick = [&]() {
      const aig::Lit l = pool[rng() % pool.size()];
      return (rng() & 1) ? aig::neg(l) : l;
    };
    const unsigned which = rng() % 100;
    aig::Lit r;
    if (which < 25)
      r = m.Xor(pick(), pick());
    else if (which < 40)
      r = m.Mux(pick(), pick(), pick());
    else
      r = m.And(pick(), pick());
    if (!aig::isConst(r))
      pool.push_back(r);
  }
}

// Exhaustive over the CIs: every clause holds under the circuit's own values,
// and BCP from the CIs reproduces every one of them.
void checkExact(const aig::Manager& m, unsigned namedOutputs,
                bool matchPatterns)
{
  const aig::Cone cone(m, namedOutputs, matchPatterns);
  const CNF cnf = aig::deriveTseitin(m, namedOutputs, matchPatterns);
  const Layout l = layoutOf(m, cone);

  ASSERT_EQ(cnf.varCount(), l.nVars);
  ASSERT_EQ(cnf.varCount(), cone.varCount());
  for (uint32_t i = 0; i < m.ciCount(); i++)
    ASSERT_EQ(cnf.varOfCi(i), 1u + i);
  for (uint32_t i = 0; i < m.outputCount(); i++)
    ASSERT_EQ(cnf.varOfCo(i), l.coVar[i]);

  const unsigned nCi = m.ciCount();
  ASSERT_LE(nCi, 12u);
  for (uint32_t bits = 0; bits < (1u << nCi); bits++)
  {
    std::vector<uint8_t> ci(nCi);
    for (unsigned i = 0; i < nCi; i++)
      ci[i] = (bits >> i) & 1;

    const std::vector<uint8_t> value = simulate(m, ci);
    const std::vector<int8_t> want = intendedValues(m, cone, l, value);

    // Are the asserted outputs all true under this assignment?  If not the
    // formula is unsatisfiable here, and the two directions swap over.
    bool assertedHold = true;
    for (uint32_t i = 0; i < cone.firstNamedOutput(); i++)
      if (!valueOf(value, m.output(i)))
        assertedHold = false;

    if (assertedHold)
    {
      for (uint64_t c = 0, n = cnf.clauseCount(); c < n; c++)
        ASSERT_TRUE(clauseSatisfied(cnf, c, want))
            << "clause " << c << " unsatisfied by the circuit's own values";
    }

    std::vector<int8_t> a(cnf.varCount(), -1);
    for (unsigned i = 0; i < nCi; i++)
      a[cnf.varOfCi(i)] = static_cast<int8_t>(ci[i]);
    const bool ok = propagate(cnf, a);

    ASSERT_EQ(ok, assertedHold)
        << "propagation should conflict exactly when an asserted output is 0";
    if (!ok)
      continue;
    for (uint32_t v = 1; v < cnf.varCount(); v++)
    {
      ASSERT_GE(a[v], 0) << "variable " << v << " left unforced";
      ASSERT_EQ(a[v], want[v]) << "variable " << v << " forced to the wrong value";
    }
  }
}

} // namespace

// The headline: on random circuits, with every output named, the CNF says
// exactly what the AIG says -- no assignment lost and none admitted.
TEST(Tseitin, NamedOutputsEncodeTheCircuitExactly)
{
  for (unsigned seed = 0; seed < 120; seed++)
  {
    std::mt19937 rng(seed);
    aig::Manager m;
    std::vector<aig::Lit> pool;
    buildRandom(m, rng, 3 + (seed % 6), 30, pool);
    for (unsigned i = 0; i < 3; i++)
      m.createOutput(pool[rng() % pool.size()]);

    ASSERT_NO_FATAL_FAILURE(checkExact(m, m.outputCount(), true)) << seed;
    ASSERT_NO_FATAL_FAILURE(checkExact(m, m.outputCount(), false)) << seed;
  }
}

// The other end of the namedOutputs split: an asserted output has no variable
// and no defining clauses, only a unit -- so the formula must be
// unsatisfiable under exactly the assignments the circuit rejects.
TEST(Tseitin, AssertedOutputIsUnsatWhereTheCircuitIsFalse)
{
  for (unsigned seed = 0; seed < 120; seed++)
  {
    std::mt19937 rng(seed);
    aig::Manager m;
    std::vector<aig::Lit> pool;
    buildRandom(m, rng, 3 + (seed % 6), 25, pool);
    m.createOutput(pool[rng() % pool.size()]);

    ASSERT_NO_FATAL_FAILURE(checkExact(m, 0, true)) << seed;
    ASSERT_NO_FATAL_FAILURE(checkExact(m, 0, false)) << seed;
  }
}

// A mixture: some outputs asserted, the trailing ones named.
TEST(Tseitin, MixedAssertedAndNamedOutputs)
{
  for (unsigned seed = 0; seed < 60; seed++)
  {
    std::mt19937 rng(seed);
    aig::Manager m;
    std::vector<aig::Lit> pool;
    buildRandom(m, rng, 3 + (seed % 4), 20, pool);
    for (unsigned i = 0; i < 4; i++)
      m.createOutput(pool[rng() % pool.size()]);

    ASSERT_NO_FATAL_FAILURE(checkExact(m, 2, true)) << seed;
  }
}

// The saving the matcher exists for, on the smallest circuit that has one.
// A MUX is three AND nodes; encoded as an ITE it is one variable and four
// clauses, and its two intermediates disappear entirely.
TEST(Tseitin, MuxCostsFourClausesInsteadOfNine)
{
  aig::Manager m;
  const aig::Lit c = m.createCi(), t = m.createCi(), e = m.createCi();
  m.createOutput(m.Mux(c, t, e));
  ASSERT_EQ(m.andCount(), 3u);

  const CNF plain = aig::deriveTseitin(m, 1, false);
  const CNF folded = aig::deriveTseitin(m, 1, true);

  // Three ANDs at 3 clauses / 7 literals each, plus the named output's two.
  EXPECT_EQ(plain.clauseCount(), 11u);
  EXPECT_EQ(plain.literalCount(), 25u);
  EXPECT_EQ(plain.varCount(), 1u + 3u + 1u + 3u);

  EXPECT_EQ(folded.clauseCount(), 6u);
  EXPECT_EQ(folded.literalCount(), 16u);
  EXPECT_EQ(folded.varCount(), 1u + 3u + 1u + 1u);
}

// Exclusive-or is the same shape with a second complementary pair, and gets
// the same four clauses out of the same emitter.
TEST(Tseitin, XorCostsFourClausesInsteadOfNine)
{
  aig::Manager m;
  const aig::Lit a = m.createCi(), b = m.createCi();
  m.createOutput(m.Xor(a, b));
  ASSERT_EQ(m.andCount(), 3u);

  EXPECT_EQ(aig::deriveTseitin(m, 1, false).clauseCount(), 11u);
  EXPECT_EQ(aig::deriveTseitin(m, 1, true).clauseCount(), 6u);
}

// The guard on the merge.  If one of the intermediates is wanted elsewhere it
// stays, and folding the parent would then add a clause rather than remove
// five -- so the matcher must decline.
TEST(Tseitin, SharedIntermediateDeclinesTheMerge)
{
  aig::Manager m;
  const aig::Lit c = m.createCi(), t = m.createCi(), e = m.createCi();
  const aig::Lit mux = m.Mux(c, t, e);
  m.createOutput(mux);
  m.createOutput(m.And(c, t)); // the MUX's own then-branch, hash-consed

  const CNF plain = aig::deriveTseitin(m, 2, false);
  const CNF folded = aig::deriveTseitin(m, 2, true);
  EXPECT_EQ(plain.clauseCount(), folded.clauseCount());
  EXPECT_EQ(plain.varCount(), folded.varCount());
}

// Over random circuits the matcher must never make a formula bigger, on any
// of the three measures, and must sometimes make it smaller.
TEST(Tseitin, MatchingNeverCostsAnything)
{
  uint64_t savedClauses = 0, savedLiterals = 0, savedVars = 0;
  for (unsigned seed = 0; seed < 200; seed++)
  {
    std::mt19937 rng(seed);
    aig::Manager m;
    std::vector<aig::Lit> pool;
    buildRandom(m, rng, 6, 80, pool);
    for (unsigned i = 0; i < 2; i++)
      m.createOutput(pool[rng() % pool.size()]);

    const CNF plain = aig::deriveTseitin(m, 0, false);
    const CNF folded = aig::deriveTseitin(m, 0, true);
    ASSERT_LE(folded.clauseCount(), plain.clauseCount()) << seed;
    ASSERT_LE(folded.literalCount(), plain.literalCount()) << seed;
    ASSERT_LE(folded.varCount(), plain.varCount()) << seed;
    savedClauses += plain.clauseCount() - folded.clauseCount();
    savedLiterals += plain.literalCount() - folded.literalCount();
    savedVars += plain.varCount() - folded.varCount();
  }
  EXPECT_GT(savedClauses, 0u);
  EXPECT_GT(savedLiterals, 0u);
  EXPECT_GT(savedVars, 0u);
}

// Only the cone of the outputs is encoded.  Nothing hashes the graph into the
// CNF, so gates nobody asked about cost nothing at all.
TEST(Tseitin, DeadNodesAreNotEncoded)
{
  aig::Manager m;
  const aig::Lit a = m.createCi(), b = m.createCi();
  const aig::Lit live = m.And(a, b);
  m.createOutput(live);

  const CNF before = aig::deriveTseitin(m);
  const uint32_t varsBefore = before.varCount();

  const aig::Lit c = m.createCi();
  for (unsigned i = 0; i < 50; i++)
    m.And(m.Xor(a, c), m.Or(b, aig::neg(c)));

  const CNF after = aig::deriveTseitin(m);
  EXPECT_EQ(after.clauseCount(), before.clauseCount());
  EXPECT_EQ(after.literalCount(), before.literalCount());
  // One more CI, and CIs are numbered whether or not they are reachable --
  // refinement names them after the fact and the numbering must not move.
  EXPECT_EQ(after.varCount(), varsBefore + 1);
  EXPECT_EQ(after.varOfCi(2), 3u);
}

// Both passes are sweeps over the node array.  A chain this deep overflows a
// default stack many times over if either of them recurses.
TEST(Tseitin, DeepChainNeedsNoStack)
{
  aig::Manager m;
  aig::Lit acc = m.createCi();
  for (unsigned i = 0; i < 1000000; i++)
    acc = m.And(acc, m.createCi());
  m.createOutput(acc);

  const CNF cnf = aig::deriveTseitin(m);
  EXPECT_EQ(cnf.clauseCount(), 3ull * 1000000 + 1);
  EXPECT_EQ(cnf.literalCount(), 7ull * 1000000 + 1);
  EXPECT_EQ(cnf.varCount(), 1u + 1000001u + 1000000u);
}

// The four constant cases.  There is no constant variable and no unit clause
// asserting one, which is the one place this encoding differs from
// Cnf_DeriveSimple on a formula neither of them can simplify further.
TEST(Tseitin, ConstantOutputs)
{
  {
    aig::Manager m;
    m.createCi();
    m.createOutput(m.constTrue());
    const CNF cnf = aig::deriveTseitin(m, 0);
    EXPECT_EQ(cnf.clauseCount(), 0u);
    EXPECT_FALSE(cnf.hasEmptyClause());
  }
  {
    aig::Manager m;
    m.createCi();
    m.createOutput(m.constFalse());
    const CNF cnf = aig::deriveTseitin(m, 0);
    EXPECT_EQ(cnf.clauseCount(), 1u);
    EXPECT_EQ(cnf.literalCount(), 0u);
    EXPECT_TRUE(cnf.hasEmptyClause());
  }
  {
    aig::Manager m;
    m.createCi();
    m.createOutput(m.constTrue());
    const CNF cnf = aig::deriveTseitin(m, 1);
    ASSERT_EQ(cnf.clauseCount(), 1u);
    EXPECT_FALSE(cnf.hasEmptyClause());
    const uint32_t v = cnf.varOfCo(0);
    EXPECT_EQ(v, 2u); // one CI, then the named output
    EXPECT_EQ(*cnf.clauseBegin(0), static_cast<int>(2 * v));
  }
  {
    aig::Manager m;
    m.createCi();
    m.createOutput(m.constFalse());
    const CNF cnf = aig::deriveTseitin(m, 1);
    ASSERT_EQ(cnf.clauseCount(), 1u);
    EXPECT_EQ(*cnf.clauseBegin(0), static_cast<int>(2 * cnf.varOfCo(0) + 1));
  }
}

// No variable 0 anywhere.  SATSolver::newVar() hands out 0 first and add(0)
// terminates a clause, so a literal naming it truncates rather than fails.
TEST(Tseitin, NoLiteralNamesVariableZero)
{
  std::mt19937 rng(7);
  aig::Manager m;
  std::vector<aig::Lit> pool;
  buildRandom(m, rng, 5, 60, pool);
  for (unsigned i = 0; i < 3; i++)
    m.createOutput(pool[rng() % pool.size()]);

  const CNF cnf = aig::deriveTseitin(m, 1);
  ASSERT_GT(cnf.clauseCount(), 0u);
  for (uint64_t i = 0, n = cnf.clauseCount(); i < n; i++)
    for (const int *p = cnf.clauseBegin(i), *stop = cnf.clauseEnd(i); p < stop;
         p++)
    {
      ASSERT_GE(*p, 2) << "literal names variable 0";
      ASSERT_LT(static_cast<uint32_t>(*p) >> 1, cnf.varCount());
    }
}

// Same circuit, two fresh managers, byte-identical arena.  Nothing in the
// writer reads an address, an allocator or a container's bucket order.
TEST(Tseitin, IsDeterministic)
{
  const auto build = [](aig::Manager& m) {
    std::mt19937 rng(99);
    std::vector<aig::Lit> pool;
    buildRandom(m, rng, 6, 200, pool);
    for (unsigned i = 0; i < 5; i++)
      m.createOutput(pool[rng() % pool.size()]);
  };

  aig::Manager a, b;
  build(a);
  build(b);
  const CNF ca = aig::deriveTseitin(a, 2);
  const CNF cb = aig::deriveTseitin(b, 2);

  ASSERT_EQ(ca.clauseCount(), cb.clauseCount());
  ASSERT_EQ(ca.literalCount(), cb.literalCount());
  ASSERT_EQ(ca.varCount(), cb.varCount());
  for (uint64_t i = 0, n = ca.clauseCount(); i < n; i++)
  {
    ASSERT_EQ(ca.clauseEnd(i) - ca.clauseBegin(i),
              cb.clauseEnd(i) - cb.clauseBegin(i));
    for (const int *p = ca.clauseBegin(i), *q = cb.clauseBegin(i),
                   *stop = ca.clauseEnd(i);
         p < stop; p++, q++)
      ASSERT_EQ(*p, *q);
  }
}

// The DIMACS file is byte-compatible with the one Cnf_DataWriteIntoFile()
// wrote, including its habit of numbering variables one above the formula's.
TEST(Tseitin, WritesDimacs)
{
  aig::Manager m;
  const aig::Lit a = m.createCi(), b = m.createCi();
  m.createOutput(m.And(a, b));

  const CNF cnf = aig::deriveTseitin(m);
  std::ostringstream out;
  cnf.writeDimacs(out);

  const std::string text = out.str();
  ASSERT_EQ(text.compare(0, 1, "c"), 0) << "the banner line is part of the format";

  std::istringstream in(text.substr(text.find('\n') + 1));
  std::string p, fmt;
  int vars = 0, clauses = 0;
  in >> p >> fmt >> vars >> clauses;
  EXPECT_EQ(p, "p");
  EXPECT_EQ(fmt, "cnf");
  EXPECT_EQ(vars, static_cast<int>(cnf.varCount()));
  EXPECT_EQ(clauses, static_cast<int>(cnf.clauseCount()));

  unsigned terminators = 0;
  int token = 0;
  while (in >> token)
  {
    if (token == 0)
      terminators++;
    else
    {
      // Variables are one above the formula's, so 1 is never named.
      EXPECT_GE(std::abs(token), 2);
      EXPECT_LE(std::abs(token), static_cast<int>(cnf.varCount()));
    }
  }
  EXPECT_EQ(terminators, cnf.clauseCount());
}

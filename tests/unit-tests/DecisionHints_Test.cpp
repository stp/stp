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

// Guards preferDecisions, the decision hints CaDiCaL (and Kissat with STP's
// IPASIR-UP extension) takes through its external propagator. Search advice can never move a verdict, so the
// checks are of three kinds: that a hint is honoured where nothing
// constrains the variable, that it changes no answer where something does,
// and that the wrapper keeps CaDiCaL's side of the contract -- a proposed
// literal has to be unassigned, and an observed variable untouched by
// inprocessing -- across the shapes the batch pipeline drives it through.
#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>

#ifdef USE_MINISAT
#include "stp/Sat/MinisatCore.h"
#endif
#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif
#ifdef USE_KISSAT
#include "stp/Sat/Kissat.h"
#endif

#include <set>
#include <vector>

using stp::SATSolver;

// The helpers are guarded by the backends whose tests use them: a build
// with neither compiles no test here, and -Werror refuses an unused helper.
#if defined(USE_CADICAL) || defined(USE_MINISAT) || defined(USE_KISSAT)
namespace
{
// A bit-vector of `width` fresh variables, least significant bit first,
// each mentioned by one clause with a fresh partner so that the backend
// treats it as part of the formula rather than a declared-but-unused
// variable, and nothing decides its value but the search.
std::vector<uint32_t> freshVector(SATSolver& s, unsigned width)
{
  std::vector<uint32_t> bits;
  for (unsigned i = 0; i < width; i++)
  {
    const uint32_t v = s.newVar();
    const uint32_t partner = s.newVar();
    SATSolver::vec_literals c;
    c.push(SATSolver::mkLit(v, false));
    c.push(SATSolver::mkLit(partner, false));
    s.addClause(c);
    bits.push_back(v);
  }
  return bits;
}

// The seeding the batch pipeline gives an array's indices: vector i gets
// the value i.
std::vector<SATSolver::DecisionHint>
countingHints(const std::vector<std::vector<uint32_t>>& vectors)
{
  std::vector<SATSolver::DecisionHint> hints;
  for (size_t i = 0; i < vectors.size(); i++)
    for (size_t bit = 0; bit < vectors[i].size(); bit++)
    {
      SATSolver::DecisionHint h;
      h.var = vectors[i][bit];
      h.value = ((i >> bit) & 1u) != 0;
      hints.push_back(h);
    }
  return hints;
}
} // namespace
#endif

#if defined(USE_CADICAL) || defined(USE_KISSAT)
namespace
{
uint64_t valueOf(SATSolver& s, const std::vector<uint32_t>& bits)
{
  uint64_t value = 0;
  for (size_t i = 0; i < bits.size(); i++)
    if (s.modelValue(bits[i]) == s.true_literal())
      value |= 1ULL << i;
  return value;
}

void addUnit(SATSolver& s, uint32_t var, bool negated)
{
  SATSolver::vec_literals c;
  c.push(SATSolver::mkLit(var, negated));
  s.addClause(c);
}
} // namespace
#endif

// The base-class default declines, and solving is unaffected.
#ifdef USE_MINISAT
TEST(DecisionHints, MinisatDeclines)
{
  stp::MinisatCore s;
  std::vector<std::vector<uint32_t>> vectors;
  vectors.push_back(freshVector(s, 2));
  EXPECT_FALSE(s.preferDecisions(countingHints(vectors)));
  bool timed_out = false;
  EXPECT_TRUE(s.solve(timed_out));
}
#endif

#ifdef USE_CADICAL

// Nothing constrains these vectors, so the search lands them wherever it
// decides first: on the hinted values, if the hints were decided before
// anything else and with the hinted polarity.
TEST(DecisionHints, CadicalDecidesHintedVectorsFirst)
{
  stp::Cadical s;
  std::vector<std::vector<uint32_t>> vectors;
  for (unsigned i = 0; i < 3; i++)
    vectors.push_back(freshVector(s, 4));
#if defined(CADICAL_MAJOR) && CADICAL_MAJOR >= 3
  ASSERT_TRUE(s.preferDecisions(countingHints(vectors)));
#else
  if (!s.preferDecisions(countingHints(vectors)))
    GTEST_SKIP() << "this CaDiCaL takes no decision hints";
#endif
  bool timed_out = false;
  ASSERT_TRUE(s.solve(timed_out));
  for (unsigned i = 0; i < 3; i++)
    EXPECT_EQ(valueOf(s, vectors[i]), i) << "vector " << i;
}

// A hint cannot move a verdict: hinted against a unit it is overruled, and
// a refutation stays a refutation however the search was seeded.
TEST(DecisionHints, CadicalVerdictsUnmovedByHints)
{
  bool timed_out = false;
  {
    stp::Cadical s;
    std::vector<std::vector<uint32_t>> vectors;
    vectors.push_back(freshVector(s, 3));
    addUnit(s, vectors[0][0], true); // bit 0 false, against the hint below
    std::vector<SATSolver::DecisionHint> hints;
    for (uint32_t v : vectors[0])
    {
      SATSolver::DecisionHint h;
      h.var = v;
      h.value = true;
      hints.push_back(h);
    }
    if (!s.preferDecisions(hints))
      GTEST_SKIP() << "this CaDiCaL takes no decision hints";
    ASSERT_TRUE(s.solve(timed_out));
    EXPECT_EQ(s.modelValue(vectors[0][0]), s.false_literal());
    EXPECT_EQ(s.modelValue(vectors[0][1]), s.true_literal());
    EXPECT_EQ(s.modelValue(vectors[0][2]), s.true_literal());
  }
  {
    stp::Cadical s;
    const uint32_t a = s.newVar();
    addUnit(s, a, false);
    addUnit(s, a, true);
    std::vector<SATSolver::DecisionHint> hints;
    SATSolver::DecisionHint h;
    h.var = a;
    h.value = true;
    hints.push_back(h);
    s.preferDecisions(hints);
    EXPECT_FALSE(s.solve(timed_out));
  }
}

// Hints are taken before the first search only: after it, a variable may
// have been touched by inprocessing and can no longer be observed, so the
// wrapper declines rather than risk CaDiCaL's contract. The caller then
// falls back to phases.
TEST(DecisionHints, CadicalDeclinesHintsAfterTheFirstSearch)
{
  bool timed_out = false;
  {
    stp::Cadical s;
    std::vector<std::vector<uint32_t>> vectors;
    vectors.push_back(freshVector(s, 2));
    ASSERT_TRUE(s.solve(timed_out));
    vectors.push_back(freshVector(s, 2));
    EXPECT_FALSE(s.preferDecisions(countingHints(vectors)));
    ASSERT_TRUE(s.solve(timed_out));
  }
  {
    stp::Cadical s;
    std::vector<std::vector<uint32_t>> vectors;
    vectors.push_back(freshVector(s, 2));
    s.simplifyOnly();
    EXPECT_FALSE(s.preferDecisions(countingHints(vectors)));
  }
}

// With factor enabled every literal travels through the declared-variable
// translation table; a hint on a raw STP index would observe and decide a
// different CaDiCaL variable than the clauses use.
TEST(DecisionHints, CadicalHintsTranslateUnderFactor)
{
  stp::Cadical s;
  if (!s.enableBVA())
    GTEST_SKIP() << "this CaDiCaL has no factor to enable";
  std::vector<std::vector<uint32_t>> vectors;
  for (unsigned i = 0; i < 3; i++)
    vectors.push_back(freshVector(s, 3));
  if (!s.preferDecisions(countingHints(vectors)))
    GTEST_SKIP() << "this CaDiCaL takes no decision hints";
  bool timed_out = false;
  ASSERT_TRUE(s.solve(timed_out));
  for (unsigned i = 0; i < 3; i++)
    EXPECT_EQ(valueOf(s, vectors[i]), i) << "vector " << i;

  // And the translation still holds for a clause added afterwards.
  addUnit(s, vectors[2][1], true); // bit 1 of vector 2, which was true
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(vectors[2][1]), s.false_literal());
}

// The refinement loop with hints in it: the trail kept between rounds, a
// model read after each, and a blocking clause added between them. The
// first model is the seeded one, and enumerating the rest finds every
// model exactly once -- the propagator's notion of what is assigned has to
// track CaDiCaL's through every backtrack for the decisions it proposes to
// be legal.
TEST(DecisionHints, CadicalHintsAcrossRefinementRounds)
{
  stp::Cadical s;
  s.enableTrailReuse(SATSolver::TrailReuse::ALL);

  const unsigned n = 4;
  std::vector<uint32_t> v;
  for (unsigned i = 0; i < n; i++)
    v.push_back(s.newVar());
  SATSolver::vec_literals someTrue, someFalse;
  for (unsigned i = 0; i < n; i++)
  {
    someTrue.push(SATSolver::mkLit(v[i], false));
    someFalse.push(SATSolver::mkLit(v[i], true));
  }
  s.addClause(someTrue);
  s.addClause(someFalse);

  // Seed the assignment 0101.
  std::vector<SATSolver::DecisionHint> hints;
  for (unsigned i = 0; i < n; i++)
  {
    SATSolver::DecisionHint h;
    h.var = v[i];
    h.value = (i % 2) == 0;
    hints.push_back(h);
  }
  if (!s.preferDecisions(hints))
    GTEST_SKIP() << "this CaDiCaL takes no decision hints";

  std::set<unsigned> seen;
  bool timed_out = false;
  unsigned rounds = 0;
  while (s.solve(timed_out))
  {
    ASSERT_FALSE(timed_out);
    unsigned model = 0;
    for (unsigned i = 0; i < n; i++)
      if (s.modelValue(v[i]) == s.true_literal())
        model |= 1u << i;
    if (rounds == 0)
    {
      EXPECT_EQ(model, 5u) << "the first candidate is the seeded one";
    }
    EXPECT_NE(model, 0u);
    EXPECT_NE(model, (1u << n) - 1);
    EXPECT_TRUE(seen.insert(model).second) << "model " << model << " twice";

    SATSolver::vec_literals block;
    for (unsigned i = 0; i < n; i++)
      block.push(SATSolver::mkLit(v[i], (model >> i) & 1u));
    s.addClause(block);
    ASSERT_LE(++rounds, 14u);
  }
  EXPECT_EQ(rounds, 14u);
}

// A hinted variable that is fixed at the root -- by a unit added before
// the hints were given, or by one added after them -- must never be
// proposed as a decision, which CaDiCaL rejects rather than ignores. The
// propagator learns both from the notifications.
TEST(DecisionHints, CadicalNeverProposesAFixedVariable)
{
  stp::Cadical s;
  const uint32_t a = s.newVar();
  const uint32_t b = s.newVar();
  const uint32_t c = s.newVar();
  const uint32_t d = s.newVar();
  SATSolver::vec_literals cd;
  cd.push(SATSolver::mkLit(c, false));
  cd.push(SATSolver::mkLit(d, false));
  s.addClause(cd);
  addUnit(s, a, true); // fixed before the hints

  std::vector<SATSolver::DecisionHint> hints;
  for (uint32_t var : {a, b, c})
  {
    SATSolver::DecisionHint h;
    h.var = var;
    h.value = true;
    hints.push_back(h);
  }
  if (!s.preferDecisions(hints))
    GTEST_SKIP() << "this CaDiCaL takes no decision hints";
  addUnit(s, b, true); // fixed after the hints, before the search

  bool timed_out = false;
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(a), s.false_literal());
  EXPECT_EQ(s.modelValue(b), s.false_literal());
  EXPECT_EQ(s.modelValue(c), s.true_literal());

  // And once more with c fixed between searches, against the kept state.
  addUnit(s, c, true);
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(c), s.false_literal());
  EXPECT_EQ(s.modelValue(d), s.true_literal());
}

#endif

#ifdef USE_KISSAT

// Kissat takes the hints through the decide callback of STP's fork; a
// Kissat without the interface declines them, as an old CaDiCaL does.
#if defined(STP_KISSAT_HAS_EXTERNAL_PROPAGATOR)
#define KISSAT_TAKES_HINTS(call) ASSERT_TRUE(call)
#else
#define KISSAT_TAKES_HINTS(call)                                              \
  if (!(call))                                                                \
  GTEST_SKIP() << "this Kissat takes no decision hints"
#endif

TEST(DecisionHints, KissatDecidesHintedVectorsFirst)
{
  stp::Kissat s;
  std::vector<std::vector<uint32_t>> vectors;
  for (unsigned i = 0; i < 3; i++)
    vectors.push_back(freshVector(s, 4));
  KISSAT_TAKES_HINTS(s.preferDecisions(countingHints(vectors)));
  bool timed_out = false;
  ASSERT_TRUE(s.solve(timed_out));
  for (unsigned i = 0; i < 3; i++)
    EXPECT_EQ(valueOf(s, vectors[i]), i) << "vector " << i;
}

TEST(DecisionHints, KissatVerdictsUnmovedByHints)
{
  bool timed_out = false;
  {
    stp::Kissat s;
    std::vector<std::vector<uint32_t>> vectors;
    vectors.push_back(freshVector(s, 3));
    addUnit(s, vectors[0][0], true); // bit 0 false, against the hint below
    std::vector<SATSolver::DecisionHint> hints;
    for (uint32_t v : vectors[0])
    {
      SATSolver::DecisionHint h;
      h.var = v;
      h.value = true;
      hints.push_back(h);
    }
    KISSAT_TAKES_HINTS(s.preferDecisions(hints));
    ASSERT_TRUE(s.solve(timed_out));
    EXPECT_EQ(s.modelValue(vectors[0][0]), s.false_literal());
    EXPECT_EQ(s.modelValue(vectors[0][1]), s.true_literal());
    EXPECT_EQ(s.modelValue(vectors[0][2]), s.true_literal());
  }
  {
    stp::Kissat s;
    const uint32_t a = s.newVar();
    addUnit(s, a, false);
    addUnit(s, a, true);
    std::vector<SATSolver::DecisionHint> hints;
    SATSolver::DecisionHint h;
    h.var = a;
    h.value = true;
    hints.push_back(h);
    s.preferDecisions(hints);
    EXPECT_FALSE(s.solve(timed_out));
  }
}

// Before the first search only, as on CaDiCaL, and never on a one-shot
// backend, which gave up the incremental mode a propagator needs.
TEST(DecisionHints, KissatDeclinesHintsAfterTheFirstSearchOrOneShot)
{
  bool timed_out = false;
  {
    stp::Kissat s;
    std::vector<std::vector<uint32_t>> vectors;
    vectors.push_back(freshVector(s, 2));
    ASSERT_TRUE(s.solve(timed_out));
    vectors.push_back(freshVector(s, 2));
    EXPECT_FALSE(s.preferDecisions(countingHints(vectors)));
    ASSERT_TRUE(s.solve(timed_out));
  }
  {
    stp::Kissat s;
    ASSERT_TRUE(s.configureOneShot());
    std::vector<std::vector<uint32_t>> vectors;
    vectors.push_back(freshVector(s, 2));
    EXPECT_FALSE(s.preferDecisions(countingHints(vectors)));
    ASSERT_TRUE(s.solve(timed_out));
  }
}

// With factor on, Kissat numbers its own variables above STP's; a hint is
// on STP's variable, and stays so for a clause added afterwards.
TEST(DecisionHints, KissatHintsUnderFactor)
{
  stp::Kissat s;
  if (!s.enableBVA())
    GTEST_SKIP() << "this Kissat has no factor to enable";
  std::vector<std::vector<uint32_t>> vectors;
  for (unsigned i = 0; i < 3; i++)
    vectors.push_back(freshVector(s, 3));
  KISSAT_TAKES_HINTS(s.preferDecisions(countingHints(vectors)));
  bool timed_out = false;
  ASSERT_TRUE(s.solve(timed_out));
  for (unsigned i = 0; i < 3; i++)
    EXPECT_EQ(valueOf(s, vectors[i]), i) << "vector " << i;
  addUnit(s, vectors[2][1], true); // bit 1 of vector 2, which was true
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(vectors[2][1]), s.false_literal());
}

// The refinement loop with hints in it, as on CaDiCaL: the first model is
// the seeded one, and enumerating the rest finds every model exactly once.
// The hints are proposed once and leave before the second search.
TEST(DecisionHints, KissatHintsAcrossRefinementRounds)
{
  stp::Kissat s;
  s.enableTrailReuse(SATSolver::TrailReuse::ALL);

  const unsigned n = 4;
  std::vector<uint32_t> v;
  for (unsigned i = 0; i < n; i++)
    v.push_back(s.newVar());
  SATSolver::vec_literals someTrue, someFalse;
  for (unsigned i = 0; i < n; i++)
  {
    someTrue.push(SATSolver::mkLit(v[i], false));
    someFalse.push(SATSolver::mkLit(v[i], true));
  }
  s.addClause(someTrue);
  s.addClause(someFalse);

  std::vector<SATSolver::DecisionHint> hints;
  for (unsigned i = 0; i < n; i++)
  {
    SATSolver::DecisionHint h;
    h.var = v[i];
    h.value = (i % 2) == 0;
    hints.push_back(h);
  }
  KISSAT_TAKES_HINTS(s.preferDecisions(hints));

  std::set<unsigned> seen;
  bool timed_out = false;
  unsigned rounds = 0;
  while (s.solve(timed_out))
  {
    ASSERT_FALSE(timed_out);
    unsigned model = 0;
    for (unsigned i = 0; i < n; i++)
      if (s.modelValue(v[i]) == s.true_literal())
        model |= 1u << i;
    if (rounds == 0)
    {
      EXPECT_EQ(model, 5u) << "the first candidate is the seeded one";
    }
    EXPECT_NE(model, 0u);
    EXPECT_NE(model, (1u << n) - 1);
    EXPECT_TRUE(seen.insert(model).second) << "model " << model << " twice";

    SATSolver::vec_literals block;
    for (unsigned i = 0; i < n; i++)
      block.push(SATSolver::mkLit(v[i], (model >> i) & 1u));
    s.addClause(block);
    ASSERT_LE(++rounds, 14u);
  }
  EXPECT_EQ(rounds, 14u);
}

// What a phase cannot do: decide in the hinted order. With (-x | -y) and
// both hinted true, the first hint decided wins and propagates the other
// false, whichever order the hints come in; phases alone would follow
// Kissat's own decision order and give one of the two orders the other
// model.
TEST(DecisionHints, KissatDecidesInTheHintedOrder)
{
  for (bool x_first : {true, false})
  {
    stp::Kissat s;
    const uint32_t x = s.newVar();
    const uint32_t y = s.newVar();
    SATSolver::vec_literals c;
    c.push(SATSolver::mkLit(x, true));
    c.push(SATSolver::mkLit(y, true));
    s.addClause(c);
    std::vector<SATSolver::DecisionHint> hints;
    for (uint32_t var : x_first ? std::vector<uint32_t>{x, y}
                                : std::vector<uint32_t>{y, x})
    {
      SATSolver::DecisionHint h;
      h.var = var;
      h.value = true;
      hints.push_back(h);
    }
    KISSAT_TAKES_HINTS(s.preferDecisions(hints));
    bool timed_out = false;
    ASSERT_TRUE(s.solve(timed_out));
    EXPECT_EQ(s.modelValue(x_first ? x : y), s.true_literal());
    EXPECT_EQ(s.modelValue(x_first ? y : x), s.false_literal());
  }
}

// A hinted variable fixed at the root, before the hints or after them, is
// never decided: the propagator learns both from the notifications and
// skips them, so the next hint takes the decision instead.
TEST(DecisionHints, KissatNeverProposesAFixedVariable)
{
  stp::Kissat s;
  const uint32_t a = s.newVar();
  const uint32_t b = s.newVar();
  const uint32_t c = s.newVar();
  const uint32_t d = s.newVar();
  SATSolver::vec_literals cd;
  cd.push(SATSolver::mkLit(c, false));
  cd.push(SATSolver::mkLit(d, false));
  s.addClause(cd);
  addUnit(s, a, true); // fixed before the hints

  std::vector<SATSolver::DecisionHint> hints;
  for (uint32_t var : {a, b, c})
  {
    SATSolver::DecisionHint h;
    h.var = var;
    h.value = true;
    hints.push_back(h);
  }
  KISSAT_TAKES_HINTS(s.preferDecisions(hints));
  addUnit(s, b, true); // fixed after the hints, before the search

  bool timed_out = false;
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(a), s.false_literal());
  EXPECT_EQ(s.modelValue(b), s.false_literal());
  EXPECT_EQ(s.modelValue(c), s.true_literal());

  addUnit(s, c, true);
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(c), s.false_literal());
  EXPECT_EQ(s.modelValue(d), s.true_literal());
}

#if defined(STP_KISSAT_HAS_EXTERNAL_PROPAGATOR)
namespace
{
// A theory that accepts everything and says nothing.
struct Silent final : SATSolver::TheoryPropagator
{
  unsigned notified = 0;
  void notifyAssigned(const std::vector<SATSolver::Lit>& lits) override
  {
    notified += lits.size();
  }
  void notifyNewLevel() override {}
  void notifyBacktrack(size_t) override {}
  bool checkFoundModel() override { return true; }
  bool takeClause(std::vector<SATSolver::Lit>&) override { return false; }
  bool failed() const override { return false; }
};
} // namespace

// Kissat has one propagator slot. A theory connecting after the hints takes
// it, and hints offered after a theory are declined for the caller to phase.
TEST(DecisionHints, KissatHintsGiveWayToATheory)
{
  bool timed_out = false;
  {
    stp::Kissat s;
    std::vector<std::vector<uint32_t>> vectors;
    vectors.push_back(freshVector(s, 3));
    ASSERT_TRUE(s.preferDecisions(countingHints(vectors)));
    Silent theory;
    ASSERT_TRUE(s.connectTheoryPropagator(&theory, {vectors[0][0]}));
    ASSERT_TRUE(s.solve(timed_out));
    EXPECT_GT(theory.notified, 0u);
    s.disconnectTheoryPropagator();
  }
  {
    stp::Kissat s;
    std::vector<std::vector<uint32_t>> vectors;
    vectors.push_back(freshVector(s, 3));
    Silent theory;
    ASSERT_TRUE(s.connectTheoryPropagator(&theory, {vectors[0][0]}));
    EXPECT_FALSE(s.preferDecisions(countingHints(vectors)));
    ASSERT_TRUE(s.solve(timed_out));
    s.disconnectTheoryPropagator();
  }
}
#endif

#endif

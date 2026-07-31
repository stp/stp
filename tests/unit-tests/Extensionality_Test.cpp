/***********
AUTHORS: Andrew Teylu

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

/*
 * Unit tests for the array-equality consistency checker (Brummayer &
 * Biere, "Lemmas on Demand for the Extensional Theory of Arrays",
 * JSAT 6 (2010), sections 7 and 8).
 *
 * Each test hand-constructs one array graph and one spurious candidate
 * assignment, mirroring the worked examples of the paper (nested-write
 * propagation, read/write congruence, propagation across equalities,
 * upward propagation, writes as accesses, read values used as write
 * indices, witness checking), and asserts the exact deterministic
 * outcome: the propagation event sequence, the rule application
 * counts, which two accesses conflict at which array, and the lemma's
 * canonical premise and conclusion. A final test covers the decision
 * table that combines the checker's verdict with STP's own model check
 * inside the refinement loop.
 */

#include "stp/Extensionality/ExtChecker.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/STPManager/STPManager.h"
#include <gtest/gtest.h>
#include <map>

using namespace stp;

namespace
{

class MapModel : public ExtModelView
{
public:
  std::map<ASTNode, ASTNode> bvVals;
  std::map<ASTNode, bool> boolVals;

  virtual ASTNode bvValue(const ASTNode& term)
  {
    std::map<ASTNode, ASTNode>::const_iterator it = bvVals.find(term);
    if (it == bvVals.end())
      FatalError("MapModel: missing bv value", term);
    return it->second;
  }
  virtual bool boolValue(const ASTNode& term)
  {
    std::map<ASTNode, bool>::const_iterator it = boolVals.find(term);
    if (it == boolVals.end())
      FatalError("MapModel: missing bool value", term);
    return it->second;
  }
};

struct ExpectedEvent
{
  ExtEvent::Kind kind;
  const char* rule;
  ASTNode destination; // null: don't check
  int access;          // -1: don't check
};

class ExtFixtureTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  ExtGraph g;
  MapModel model;
  size_t nextRecord = 0;

  ASTNode arr(const char* name)
  {
    return mgr.CreateSymbol(name, 2, 2);
  }
  ASTNode bv(const char* name, int val)
  {
    ASTNode s = mgr.CreateSymbol(name, 0, 2);
    model.bvVals[s] = mgr.CreateBVConst(2, val);
    return s;
  }
  ASTNode boolSym(const char* name, bool val)
  {
    ASTNode s = mgr.CreateSymbol(name, 0, 0);
    model.boolVals[s] = val;
    return s;
  }
  ASTNode c2(int val) { return mgr.CreateBVConst(2, val); }

  ASTNode write(const ASTNode& base, const ASTNode& idx, const ASTNode& val)
  {
    NodeFactory* hf = mgr.hashingNodeFactory;
    ASTNode w = hf->CreateArrayTerm(WRITE, 2, 2,
                                    {base, idx, val});
    ExtWriteNode info;
    info.write = w;
    info.base = base;
    info.indexTerm = idx;
    info.indexName = idx;
    g.writes[w] = info;
    g.writeParents[base].push_back(w);
    return w;
  }

  // Access value symbol doubles as the read-abstraction symbol.
  size_t readAccess(const ASTNode& array, const ASTNode& idx,
                    const ASTNode& valueSym)
  {
    ExtAccess a;
    a.id = g.accesses.size();
    a.isWrite = false;
    a.site = array;
    a.indexTerm = idx;
    a.valueTerm = valueSym;
    a.indexName = idx;
    a.valueName = valueSym;
    g.accesses.push_back(a);
    return a.id;
  }

  size_t writeAccess(const ASTNode& w)
  {
    ExtAccess a;
    a.id = g.accesses.size();
    a.isWrite = true;
    a.site = w;
    a.indexTerm = w[1];
    a.valueTerm = w[2];
    a.indexName = w[1];
    a.valueName = w[2];
    g.accesses.push_back(a);
    return a.id;
  }

  ASTNode eqEdge(const ASTNode& left, const ASTNode& right, const char* name,
                 bool truth)
  {
    ASTNode proxy = boolSym(name, truth);
    ExtEqEdge e;
    e.record = nextRecord++;
    e.left = left;
    e.right = right;
    e.proxy = proxy;
    const size_t idx = g.eqEdges.size();
    g.eqEdges.push_back(e);
    g.eqAdjacency[left].push_back(idx);
    if (!(left == right))
      g.eqAdjacency[right].push_back(idx);
    return proxy;
  }

  void witness(const ASTNode& proxy, const ASTNode& lambda,
               const ASTNode& leftVal, const ASTNode& rightVal)
  {
    ExtWitness w;
    // record id: position by insertion; matches eqEdge creation order.
    w.record = g.witnesses.size();
    w.proxy = proxy;
    w.index = lambda;
    w.leftValue = leftVal;
    w.rightValue = rightVal;
    g.witnesses.push_back(w);
  }

  ExtCheckResult run() { return ExtChecker::check(g, model, true); }

  static bool hasNeGuard(const std::vector<ExtLemmaAtom>& premise,
                         const ASTNode& a, const ASTNode& b)
  {
    for (size_t i = 0; i < premise.size(); i++)
      if (premise[i].op == ExtLemmaAtom::BV_NE && premise[i].a == a &&
          premise[i].b == b)
        return true;
    return false;
  }
  static bool hasEqGuard(const std::vector<ExtLemmaAtom>& premise,
                         const ASTNode& a, const ASTNode& b)
  {
    for (size_t i = 0; i < premise.size(); i++)
      if (premise[i].op == ExtLemmaAtom::BV_EQ && premise[i].a == a &&
          premise[i].b == b)
        return true;
    return false;
  }
  static bool hasProxyGuard(const std::vector<ExtLemmaAtom>& premise,
                            const ASTNode& proxy)
  {
    for (size_t i = 0; i < premise.size(); i++)
      if (premise[i].op == ExtLemmaAtom::BOOL_LIT &&
          premise[i].boolTerm == proxy)
        return true;
    return false;
  }
  static bool hasArrayEqGuard(const std::vector<ExtLemmaAtom>& premise,
                              const ASTNode& a, const ASTNode& b)
  {
    for (size_t i = 0; i < premise.size(); i++)
      if (premise[i].op == ExtLemmaAtom::ARRAY_EQ && premise[i].a == a &&
          premise[i].b == b)
        return true;
    return false;
  }

  void expectStats(const ExtCheckResult& r,
                   const std::map<std::string, int>& expected)
  {
    EXPECT_EQ(expected, r.stats);
  }

  void expectEvents(const ExtCheckResult& r,
                    const std::vector<ExpectedEvent>& expected)
  {
    ASSERT_EQ(expected.size(), r.events.size());
    matchEvents(r, expected);
  }

  // The pass runs its fixed point to completion, so the tail of the
  // event log is whatever exploration remained after the first
  // conflict -- incidental, and brittle to pin. What the order tests
  // are about is the discovery order up to that conflict: the FIFO
  // work list makes it breadth-first, so the conflict fires on a
  // shortest propagation path (section 11.1). Pin exactly that prefix.
  void expectEventPrefix(const ExtCheckResult& r,
                         const std::vector<ExpectedEvent>& expected)
  {
    ASSERT_LE(expected.size(), r.events.size());
    matchEvents(r, expected);
    // The prefix must be the whole story up to the first conflict.
    EXPECT_EQ(ExtEvent::CONFLICT, expected.back().kind);
    for (size_t i = 0; i + 1 < expected.size(); i++)
      EXPECT_NE(ExtEvent::CONFLICT, r.events[i].kind) << "event " << i;
  }

  void matchEvents(const ExtCheckResult& r,
                   const std::vector<ExpectedEvent>& expected)
  {
    for (size_t i = 0; i < expected.size(); i++)
    {
      EXPECT_EQ(expected[i].kind, r.events[i].kind) << "event " << i;
      EXPECT_STREQ(expected[i].rule, r.events[i].rule) << "event " << i;
      if (!expected[i].destination.IsNull())
      {
        EXPECT_EQ(expected[i].destination, r.events[i].destination)
            << "event " << i;
      }
      if (expected[i].access >= 0)
      {
        EXPECT_EQ((size_t)expected[i].access, r.events[i].access)
            << "event " << i;
      }
    }
  }

  // The rule that fired the first conflict.
  static const char* firstConflictRule(const ExtCheckResult& r)
  {
    for (size_t i = 0; i < r.events.size(); i++)
      if (r.events[i].kind == ExtEvent::CONFLICT)
        return r.events[i].rule;
    return "<no conflict event>";
  }
};

// Example 1 of the paper: the simplest congruence conflict -- two reads of one
// array at concretely equal indexes with different values. The conflict
// fires while seeding the second access, so both chi are empty and the
// lemma premise is the index equality alone: i = j -> r1 = r2.
TEST_F(ExtFixtureTest, ReadReadCongruenceOneArray)
{
  ASTNode A = arr("A");
  ASTNode i = bv("i", 0), j = bv("j", 0);
  ASTNode r1 = bv("r1", 1), r2 = bv("r2", 2);

  size_t a1 = readAccess(A, i, r1);
  size_t a2 = readAccess(A, j, r2);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 1}, {"insertions", 1}, {"seeds", 1}});
  expectEvents(r, {{ExtEvent::SEED, "I_READ", A, (int)a1},
                   {ExtEvent::CONFLICT, "I_READ", A, (int)a2}});

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(A, c.commonArray);
  EXPECT_EQ(a1, c.leftAccess);
  EXPECT_EQ(a2, c.rightAccess);
  EXPECT_EQ(c2(0), c.indexValue);
  EXPECT_EQ(c2(1), c.leftValue);
  EXPECT_EQ(c2(2), c.rightValue);
  ASSERT_EQ(1u, c.abstractPremise.size());
  EXPECT_TRUE(hasEqGuard(c.abstractPremise, i, j));
  EXPECT_EQ(r1, c.abstractConclusionA);
  EXPECT_EQ(r2, c.abstractConclusionB);
}

// One pass reports every conflict it finds, not just the earliest.
// Two unrelated arrays, each with its own read-read congruence
// conflict: nothing connects them, so the two lemmas share no atom and
// neither can be derived from the other. A pass that stopped at the
// first would hand back one lemma and need a whole extra SAT solve to
// discover the other -- which is what made refinement on
// if-then-else-heavy queries spend thousands of rounds emitting one
// clause each.
TEST_F(ExtFixtureTest, IndependentConflictsAreAllReported)
{
  ASTNode A = arr("A"), B = arr("B");
  ASTNode i = bv("i", 0), j = bv("j", 0);
  ASTNode p = bv("p", 1), q = bv("q", 1);
  ASTNode r1 = bv("r1", 1), r2 = bv("r2", 2);
  ASTNode s1 = bv("s1", 1), s2 = bv("s2", 3);

  size_t a1 = readAccess(A, i, r1);
  size_t a2 = readAccess(A, j, r2);
  size_t b1 = readAccess(B, p, s1);
  size_t b2 = readAccess(B, q, s2);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  ASSERT_EQ(2u, r.conflicts.size());

  // conflicts[0] is what a first-conflict-wins pass would have returned
  EXPECT_EQ(r.conflicts[0].commonArray, r.conflict.commonArray);
  EXPECT_EQ(r.conflicts[0].leftAccess, r.conflict.leftAccess);

  EXPECT_EQ(A, r.conflicts[0].commonArray);
  EXPECT_EQ(a1, r.conflicts[0].leftAccess);
  EXPECT_EQ(a2, r.conflicts[0].rightAccess);
  EXPECT_EQ(r1, r.conflicts[0].abstractConclusionA);
  EXPECT_EQ(r2, r.conflicts[0].abstractConclusionB);

  EXPECT_EQ(B, r.conflicts[1].commonArray);
  EXPECT_EQ(b1, r.conflicts[1].leftAccess);
  EXPECT_EQ(b2, r.conflicts[1].rightAccess);
  EXPECT_EQ(s1, r.conflicts[1].abstractConclusionA);
  EXPECT_EQ(s2, r.conflicts[1].abstractConclusionB);

  // Each lemma stands alone: its own index equality, nothing shared.
  ASSERT_EQ(1u, r.conflicts[0].abstractPremise.size());
  ASSERT_EQ(1u, r.conflicts[1].abstractPremise.size());
  EXPECT_TRUE(hasEqGuard(r.conflicts[0].abstractPremise, i, j));
  EXPECT_TRUE(hasEqGuard(r.conflicts[1].abstractPremise, p, q));
}

// A false array equality whose witness reads differ: a consistent
// candidate (the witness of preprocessing step 1 is satisfied).
TEST_F(ExtFixtureTest, NegativeEqualityConsistent)
{
  ASTNode A = arr("A"), B = arr("B");
  ASTNode lam = bv("z_lam_eqAB", 2);
  ASTNode wL = bv("z_wL_eqAB", 1), wR = bv("z_wR_eqAB", 3);
  ASTNode eqAB = eqEdge(A, B, "eqAB", false);
  witness(eqAB, lam, wL, wR);
  size_t aL = readAccess(A, lam, wL);
  size_t aR = readAccess(B, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONSISTENT, r.status);
  expectStats(r, {{"insertions", 2}, {"seeds", 2}, {"witness_checks", 1}});
  expectEvents(r, {{ExtEvent::SEED, "I_READ", A, (int)aL},
                   {ExtEvent::SEED, "I_READ", B, (int)aR},
                   {ExtEvent::WITNESS_CHECK, "WITNESS", ASTNode(), -1}});
  // the consistent fixed point reports each array's observed contents
  ASSERT_EQ(1u, r.observed.count(A));
  ASSERT_EQ(1u, r.observed.find(A)->second.size());
  EXPECT_EQ(c2(2), r.observed.find(A)->second[0].first);
  EXPECT_EQ(c2(1), r.observed.find(A)->second[0].second);
}

// A false array equality whose witness reads are EQUAL: impossible if
// the witness constraint was really bit-blasted, so the checker
// reports it as a violation rather than a refinable conflict.
TEST_F(ExtFixtureTest, NegativeEqualityWitnessViolation)
{
  ASTNode A = arr("A"), B = arr("B");
  ASTNode lam = bv("z_lam_eqAB", 2);
  ASTNode wL = bv("z_wL_eqAB", 1), wR = bv("z_wR_eqAB", 1);
  ASTNode eqAB = eqEdge(A, B, "eqAB", false);
  witness(eqAB, lam, wL, wR);
  readAccess(A, lam, wL);
  readAccess(B, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::WITNESS_VIOLATION, r.status);
  EXPECT_EQ(0u, r.violatedRecord);
  expectStats(r, {{"insertions", 2}, {"seeds", 2}, {"witness_checks", 1}});
}

// A true array equality on a satisfiable candidate: the checker
// reaches CONSISTENT through the witness loop -- which must skip
// records whose equality sigma assigns true, however their witness
// values compare -- and the export carries the ordinary read across
// the equality into both arrays' observed contents. Every other test
// with a true equality conflicts before the witness loop runs, so
// this is what pins the loop's proxy guard: treating a true
// equality's (necessarily equal) witness reads as a violation would
// abort every satisfiable query containing a true array equality.
TEST_F(ExtFixtureTest, TrueEqualityConsistentAndExported)
{
  ASTNode A = arr("A"), B = arr("B");
  ASTNode i = bv("i", 0);
  ASTNode v = bv("v", 3);
  ASTNode eqAB = eqEdge(A, B, "eqAB", true);
  ASTNode lam = bv("z_lam_eqAB", 2);
  // equal arrays agree everywhere, the witness index included
  ASTNode wL = bv("z_wL_eqAB", 1), wR = bv("z_wR_eqAB", 1);
  witness(eqAB, lam, wL, wR);

  // seed order: v, z_wL_eqAB, z_wR_eqAB
  size_t aX = readAccess(A, i, v);
  size_t aL = readAccess(A, lam, wL);
  size_t aR = readAccess(B, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONSISTENT, r.status);
  expectStats(r, {{"insertions", 4},
                  {"propagations", 1},
                  {"rule_R_EQ", 1},
                  {"seeds", 3},
                  {"skipped_represented", 2},
                  {"skipped_seen", 1},
                  {"witness_checks", 1}});
  expectEvents(r, {{ExtEvent::SEED, "I_READ", A, (int)aX},
                   {ExtEvent::SEED, "I_READ", A, (int)aL},
                   {ExtEvent::SEED, "I_READ", B, (int)aR},
                   {ExtEvent::PROPAGATE, "R_EQ", B, (int)aX},
                   {ExtEvent::SKIP_REPRESENTED, "R_EQ", B, (int)aL},
                   {ExtEvent::SKIP_REPRESENTED, "L_EQ", A, (int)aR},
                   {ExtEvent::SKIP_SEEN, "L_EQ", A, (int)aX},
                   {ExtEvent::WITNESS_CHECK, "WITNESS", ASTNode(), -1}});

  // Both arrays observe both points: the ordinary read's pair arrived
  // at B across the true equality, and each witness read represents
  // the other side's at its own array.
  ASSERT_EQ(1u, r.observed.count(A));
  ASSERT_EQ(1u, r.observed.count(B));
  const std::vector<std::pair<ASTNode, ASTNode>>& obsA =
      r.observed.find(A)->second;
  const std::vector<std::pair<ASTNode, ASTNode>>& obsB =
      r.observed.find(B)->second;
  ASSERT_EQ(2u, obsA.size());
  EXPECT_EQ(c2(0), obsA[0].first);
  EXPECT_EQ(c2(3), obsA[0].second);
  EXPECT_EQ(c2(2), obsA[1].first);
  EXPECT_EQ(c2(1), obsA[1].second);
  ASSERT_EQ(2u, obsB.size());
  EXPECT_EQ(c2(2), obsB[0].first);
  EXPECT_EQ(c2(1), obsB[0].second);
  EXPECT_EQ(c2(0), obsB[1].first);
  EXPECT_EQ(c2(3), obsB[1].second);
}

// Examples 2/3 of the paper: reads propagate down through nested
// writes (rule D), collecting the write-index disequalities that end
// up in the lemma premise.
TEST_F(ExtFixtureTest, NestedWriteDownConflict)
{
  ASTNode A = arr("A");
  ASTNode i = bv("i", 0), k = bv("k", 0);
  ASTNode j1 = bv("j1", 2), j2 = bv("j2", 1), j3 = bv("j3", 3);
  ASTNode e1 = bv("e1", 0), e2 = bv("e2", 0), e3 = bv("e3", 0);
  ASTNode w1 = write(A, j1, e1);
  ASTNode w2 = write(w1, j2, e2);
  ASTNode w3 = write(A, j3, e3);
  ASTNode r1 = bv("r1", 1), r2 = bv("r2", 2);

  // seed order: r1, r2, w1, w2, w3
  size_t ar1 = readAccess(w2, i, r1);
  size_t ar2 = readAccess(w3, k, r2);
  size_t aw1 = writeAccess(w1);
  size_t aw2 = writeAccess(w2);
  size_t aw3 = writeAccess(w3);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 2},
                  {"insertions", 8},
                  {"propagations", 3},
                  {"rule_D_WRITE", 2},
                  {"rule_U_WRITE", 1},
                  {"seeds", 5},
                  {"skipped_seen", 3}});
  // ar1 reaches A downward and collides with ar2 there; carrying on,
  // ar2 reaches w2 upward and collides with ar1 from the other side.
  // One contradiction, two lemmas -- their write-index disequalities
  // differ, so neither clause subsumes the other.
  EXPECT_EQ(2u, r.conflicts.size());
  expectEventPrefix(r, {{ExtEvent::SEED, "I_READ", w2, (int)ar1},
                        {ExtEvent::SEED, "I_READ", w3, (int)ar2},
                        {ExtEvent::SEED, "I_WRITE", w1, (int)aw1},
                        {ExtEvent::SEED, "I_WRITE", w2, (int)aw2},
                        {ExtEvent::SEED, "I_WRITE", w3, (int)aw3},
                        {ExtEvent::PROPAGATE, "D_WRITE", w1, (int)ar1},
                        {ExtEvent::PROPAGATE, "D_WRITE", A, (int)ar2},
                        {ExtEvent::PROPAGATE, "U_WRITE", w2, (int)aw1},
                        {ExtEvent::CONFLICT, "D_WRITE", A, (int)ar1}});

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(A, c.commonArray);
  EXPECT_EQ(ar2, c.leftAccess);
  EXPECT_EQ(ar1, c.rightAccess);
  EXPECT_EQ(c2(0), c.indexValue);
  EXPECT_EQ(c2(2), c.leftValue);
  EXPECT_EQ(c2(1), c.rightValue);
  EXPECT_TRUE(hasNeGuard(c.abstractPremise, i, j2));
  EXPECT_TRUE(hasNeGuard(c.abstractPremise, i, j1));
  EXPECT_TRUE(hasNeGuard(c.abstractPremise, k, j3));
  EXPECT_TRUE(hasEqGuard(c.abstractPremise, k, i));
  EXPECT_EQ(4u, c.abstractPremise.size());
  EXPECT_EQ(r2, c.abstractConclusionA);
  EXPECT_EQ(r1, c.abstractConclusionB);
}

// Example 4 of the paper: a true array equality propagates reads
// across it (rules R/L), and the equality appears positively in the
// lemma.
TEST_F(ExtFixtureTest, PositiveReadEqualityConflict)
{
  ASTNode A = arr("A"), B = arr("B");
  ASTNode i = bv("i", 0), j = bv("j", 0);
  ASTNode rA = bv("rA", 1), rB = bv("rB", 2);
  ASTNode eqAB = eqEdge(A, B, "eqAB", true);
  ASTNode lam = bv("z_lam_eqAB", 1);
  ASTNode wL = bv("z_wL_eqAB", 0), wR = bv("z_wR_eqAB", 0);
  witness(eqAB, lam, wL, wR);

  // seed order: rA, rB, z_wL_eqAB, z_wR_eqAB
  size_t aA = readAccess(A, i, rA);
  size_t aB = readAccess(B, j, rB);
  readAccess(A, lam, wL);
  readAccess(B, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  // The collision is symmetric across the equality: each read crosses
  // to the other array and meets the other read there.
  expectStats(r, {{"conflicts", 2},
                  {"insertions", 4},
                  {"seeds", 4},
                  {"skipped_represented", 2}});
  EXPECT_EQ(2u, r.conflicts.size());

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(B, c.commonArray);
  EXPECT_EQ(aB, c.leftAccess);
  EXPECT_EQ(aA, c.rightAccess);
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, eqAB));
  EXPECT_TRUE(hasEqGuard(c.abstractPremise, j, i));
  EXPECT_EQ(2u, c.abstractPremise.size());
  EXPECT_EQ(rB, c.abstractConclusionA);
  EXPECT_EQ(rA, c.abstractConclusionB);
  // the conflict fires while seeding rA's R_EQ propagation
  EXPECT_STREQ("R_EQ", firstConflictRule(r));
}

// Example 7 of the paper: read values used as write indices/values;
// the conflicting pair is two write accesses, exercising writes as
// accesses (section 11.4).
TEST_F(ExtFixtureTest, ReadValuesWriteIndicesConflict)
{
  ASTNode A = arr("A"), B = arr("B"), C = arr("C");
  ASTNode i1 = bv("i1", 0), i2 = bv("i2", 1), k = bv("k", 1), e = bv("e", 3);
  ASTNode r1 = bv("r1", 1), r2 = bv("r2", 2);
  ASTNode w1 = write(B, r1, r2);
  ASTNode w2 = write(C, k, e);
  ASTNode eqW = eqEdge(w1, w2, "eqW", true);
  ASTNode lam = bv("z_lam_eqW", 0);
  ASTNode wL = bv("z_wL_eqW", 0), wR = bv("z_wR_eqW", 0);
  witness(eqW, lam, wL, wR);

  // seed order: r1, r2, w1, w2, z_wL_eqW, z_wR_eqW
  readAccess(A, i1, r1);
  readAccess(A, i2, r2);
  size_t aw1 = writeAccess(w1);
  size_t aw2 = writeAccess(w2);
  readAccess(w1, lam, wL);
  readAccess(w2, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 2},
                  {"insertions", 8},
                  {"propagations", 2},
                  {"rule_D_WRITE", 2},
                  {"seeds", 6},
                  {"skipped_represented", 2},
                  {"skipped_seen", 2}});
  EXPECT_EQ(2u, r.conflicts.size());

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(w2, c.commonArray);
  EXPECT_EQ(aw2, c.leftAccess);
  EXPECT_EQ(aw1, c.rightAccess);
  EXPECT_EQ(c2(1), c.indexValue);
  EXPECT_EQ(c2(3), c.leftValue);
  EXPECT_EQ(c2(2), c.rightValue);
  EXPECT_TRUE(hasEqGuard(c.abstractPremise, k, r1));
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, eqW));
  EXPECT_EQ(2u, c.abstractPremise.size());
  EXPECT_EQ(e, c.abstractConclusionA);
  EXPECT_EQ(r2, c.abstractConclusionB);
}

// A read that propagates down onto a write whose index it matches
// conflicts with the write's own access (axiom A2 through the access
// representation).
TEST_F(ExtFixtureTest, ReadWriteHitConflict)
{
  ASTNode A = arr("A");
  ASTNode i = bv("i", 1), j1 = bv("j1", 1), j2 = bv("j2", 2);
  ASTNode e1 = bv("e1", 3), e2 = bv("e2", 0);
  ASTNode w1 = write(A, j1, e1);
  ASTNode w2 = write(w1, j2, e2);
  ASTNode r1 = bv("r1", 0);

  // seed order: r1, w1, w2
  size_t ar1 = readAccess(w2, i, r1);
  size_t aw1 = writeAccess(w1);
  writeAccess(w2);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  // Found twice: the read propagates down through w2 onto w1, and w1's
  // write access propagates up over w2 onto the read. The two lemmas
  // carry different write-index disequalities (i != j2 against
  // j1 != j2), so neither subsumes the other.
  expectStats(r, {{"conflicts", 2}, {"insertions", 3}, {"seeds", 3}});
  EXPECT_EQ(2u, r.conflicts.size());

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(w1, c.commonArray);
  EXPECT_EQ(aw1, c.leftAccess);
  EXPECT_EQ(ar1, c.rightAccess);
  EXPECT_TRUE(hasEqGuard(c.abstractPremise, j1, i));
  EXPECT_TRUE(hasNeGuard(c.abstractPremise, i, j2));
  EXPECT_EQ(2u, c.abstractPremise.size());
  EXPECT_EQ(e1, c.abstractConclusionA);
  EXPECT_EQ(r1, c.abstractConclusionB);
}

// Two chained true equalities a = b and b = c: breadth-first
// discovery drives each access one edge inward, so they meet at the
// middle array and the lemma still carries both equalities -- one
// contributed by each side's path.
TEST_F(ExtFixtureTest, TransitiveEqualityConflict)
{
  ASTNode A = arr("A"), B = arr("B"), C = arr("C");
  ASTNode i = bv("i", 0), j = bv("j", 0);
  ASTNode rA = bv("rA", 1), rC = bv("rC", 2);
  ASTNode eqAB = eqEdge(A, B, "eqAB", true);
  ASTNode eqBC = eqEdge(B, C, "eqBC", true);
  ASTNode lamAB = bv("z_lam_eqAB", 1);
  ASTNode wLAB = bv("z_wL_eqAB", 0), wRAB = bv("z_wR_eqAB", 0);
  ASTNode lamBC = bv("z_lam_eqBC", 2);
  ASTNode wLBC = bv("z_wL_eqBC", 3), wRBC = bv("z_wR_eqBC", 3);
  witness(eqAB, lamAB, wLAB, wRAB);
  witness(eqBC, lamBC, wLBC, wRBC);

  // seed order: rA, rC, z_wL_eqAB, z_wL_eqBC, z_wR_eqAB, z_wR_eqBC
  size_t aA = readAccess(A, i, rA);
  size_t aC = readAccess(C, j, rC);
  readAccess(A, lamAB, wLAB);
  readAccess(B, lamBC, wLBC);
  readAccess(B, lamAB, wRAB);
  readAccess(C, lamBC, wRBC);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 2},
                  {"insertions", 9},
                  {"propagations", 3},
                  {"rule_L_EQ", 1},
                  {"rule_R_EQ", 2},
                  {"seeds", 6},
                  {"skipped_represented", 4},
                  {"skipped_seen", 3}});
  EXPECT_EQ(2u, r.conflicts.size());

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(B, c.commonArray);
  EXPECT_EQ(aA, c.leftAccess);
  EXPECT_EQ(aC, c.rightAccess);
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, eqAB));
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, eqBC));
  EXPECT_TRUE(hasEqGuard(c.abstractPremise, i, j));
  EXPECT_EQ(3u, c.abstractPremise.size());
  EXPECT_EQ(rA, c.abstractConclusionA);
  EXPECT_EQ(rC, c.abstractConclusionB);
  EXPECT_STREQ("L_EQ", r.events.back().rule);
}

// One access crossing two successive equality edges before its
// conflict fires -- the complement of the meet-in-the-middle shape
// above, which breadth-first search produces whenever both ends are
// plain reads. Here the far access reached C by stepping down out of
// a write, so its equality expansion trails one hop behind and the
// near access completes the whole two-edge chain itself: the
// conflicting arrival carries both equality proxies on its own path,
// the resident access only its write-index guard.
TEST_F(ExtFixtureTest, OneAccessCrossesTwoEqualityEdges)
{
  ASTNode A = arr("A"), B = arr("B"), C = arr("C");
  ASTNode ix = bv("ix", 0), iy = bv("iy", 0);
  ASTNode jW = bv("jW", 1), eW = bv("eW", 3);
  ASTNode rx = bv("rx", 1), ry = bv("ry", 2);
  ASTNode w = write(C, jW, eW); // a write stacked on C
  ASTNode eqAB = eqEdge(A, B, "eqAB", true);
  ASTNode eqBC = eqEdge(B, C, "eqBC", true);
  ASTNode lamAB = bv("z_lam_eqAB", 2);
  ASTNode wLAB = bv("z_wL_eqAB", 0), wRAB = bv("z_wR_eqAB", 0);
  ASTNode lamBC = bv("z_lam_eqBC", 3);
  ASTNode wLBC = bv("z_wL_eqBC", 1), wRBC = bv("z_wR_eqBC", 1);
  witness(eqAB, lamAB, wLAB, wRAB);
  witness(eqBC, lamBC, wLBC, wRBC);

  // seed order: rx, ry, w, then the witness reads
  size_t aX = readAccess(A, ix, rx);
  size_t aY = readAccess(w, iy, ry);
  writeAccess(w);
  readAccess(A, lamAB, wLAB);
  readAccess(B, lamAB, wRAB);
  readAccess(B, lamBC, wLBC);
  readAccess(C, lamBC, wRBC);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 2},
                  {"insertions", 13},
                  {"propagations", 6},
                  {"rule_D_WRITE", 1},
                  {"rule_L_EQ", 1},
                  {"rule_R_EQ", 2},
                  {"rule_U_WRITE", 2},
                  {"seeds", 7},
                  {"skipped_represented", 4},
                  {"skipped_seen", 6}});
  EXPECT_EQ(2u, r.conflicts.size());

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(C, c.commonArray);
  EXPECT_EQ(aY, c.leftAccess);
  EXPECT_EQ(aX, c.rightAccess);
  // the arriving access's path is the two successive equality edges,
  // in traversal order
  ASSERT_EQ(2u, c.rightGuards.size());
  EXPECT_EQ(ExtGuard::EQ_PROXY, c.rightGuards[0].kind);
  EXPECT_EQ(eqAB, c.rightGuards[0].proxy);
  EXPECT_EQ(ExtGuard::EQ_PROXY, c.rightGuards[1].kind);
  EXPECT_EQ(eqBC, c.rightGuards[1].proxy);
  // the resident access left its write with a single index guard
  ASSERT_EQ(1u, c.leftGuards.size());
  EXPECT_EQ(ExtGuard::INDEX_NE, c.leftGuards[0].kind);

  EXPECT_TRUE(hasEqGuard(c.abstractPremise, iy, ix));
  EXPECT_TRUE(hasNeGuard(c.abstractPremise, iy, jW));
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, eqAB));
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, eqBC));
  EXPECT_EQ(4u, c.abstractPremise.size());
  EXPECT_EQ(ry, c.abstractConclusionA);
  EXPECT_EQ(rx, c.abstractConclusionB);
  EXPECT_STREQ("R_EQ", firstConflictRule(r));
}

// Example 5 of the paper: upward propagation over a write (rule U),
// across the equality of the two writes (R/L), then downward again
// (rule D) -- the case that shows why upward propagation is needed for
// extensionality.
TEST_F(ExtFixtureTest, UpEqualityDownConflict)
{
  ASTNode A = arr("A"), B = arr("B");
  ASTNode i = bv("i", 1), j = bv("j", 2), k = bv("k", 0);
  ASTNode e1 = bv("e1", 3), e2 = bv("e2", 3);
  ASTNode w1 = write(A, i, e1);
  ASTNode w2 = write(B, j, e2);
  ASTNode rA = bv("rA", 1), rB = bv("rB", 2);
  ASTNode eqW = eqEdge(w1, w2, "eqW", true);
  ASTNode lam = bv("z_lam_eqW", 3);
  ASTNode wL = bv("z_wL_eqW", 0), wR = bv("z_wR_eqW", 0);
  witness(eqW, lam, wL, wR);

  // seed order: rA, rB, w1, w2, z_wL_eqW, z_wR_eqW
  size_t aA = readAccess(A, k, rA);
  size_t aB = readAccess(B, k, rB);
  size_t aw1 = writeAccess(w1);
  size_t aw2 = writeAccess(w2);
  size_t aL = readAccess(w1, lam, wL);
  size_t aR = readAccess(w2, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  // The two witness reads carry equal concrete values, so each is a
  // represented duplicate of the other side's witness read when it
  // crosses the equality (section 11.2) and is dropped there.
  expectStats(r, {{"conflicts", 2},
                  {"insertions", 14},
                  {"propagations", 8},
                  {"rule_D_WRITE", 4},
                  {"rule_L_EQ", 1},
                  {"rule_R_EQ", 1},
                  {"rule_U_WRITE", 2},
                  {"seeds", 6},
                  {"skipped_represented", 2},
                  {"skipped_seen", 8}});
  // aA crosses the equality rightward into w2 and collides with aB;
  // the pass carries on and aB crosses leftward into w1, colliding
  // with aA. Mirror-image lemmas over the same equality proxy.
  EXPECT_EQ(2u, r.conflicts.size());
  expectEventPrefix(r, {{ExtEvent::SEED, "I_READ", A, (int)aA},
                        {ExtEvent::SEED, "I_READ", B, (int)aB},
                        {ExtEvent::SEED, "I_WRITE", w1, (int)aw1},
                        {ExtEvent::SEED, "I_WRITE", w2, (int)aw2},
                        {ExtEvent::SEED, "I_READ", w1, (int)aL},
                        {ExtEvent::SEED, "I_READ", w2, (int)aR},
                        {ExtEvent::PROPAGATE, "U_WRITE", w1, (int)aA},
                        {ExtEvent::PROPAGATE, "U_WRITE", w2, (int)aB},
                        {ExtEvent::PROPAGATE, "R_EQ", w2, (int)aw1},
                        {ExtEvent::PROPAGATE, "L_EQ", w1, (int)aw2},
                        {ExtEvent::PROPAGATE, "D_WRITE", A, (int)aL},
                        {ExtEvent::SKIP_REPRESENTED, "R_EQ", w2, (int)aL},
                        {ExtEvent::PROPAGATE, "D_WRITE", B, (int)aR},
                        {ExtEvent::SKIP_REPRESENTED, "L_EQ", w1, (int)aR},
                        {ExtEvent::SKIP_SEEN, "D_WRITE", A, (int)aA},
                        {ExtEvent::CONFLICT, "R_EQ", w2, (int)aA}});

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(w2, c.commonArray);
  EXPECT_EQ(aB, c.leftAccess);
  EXPECT_EQ(aA, c.rightAccess);
  EXPECT_TRUE(hasNeGuard(c.abstractPremise, k, i));
  EXPECT_TRUE(hasNeGuard(c.abstractPremise, k, j));
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, eqW));
  // the reflexive index equality k = k is canonicalized away
  EXPECT_EQ(3u, c.abstractPremise.size());
  EXPECT_EQ(rB, c.abstractConclusionA);
  EXPECT_EQ(rA, c.abstractConclusionB);
}

// Two equal writes at concretely equal indices with different values,
// and not a single read in the formula: only writes-as-accesses can
// find this conflict.
TEST_F(ExtFixtureTest, WriteWriteEqualityConflict)
{
  ASTNode A = arr("A"), B = arr("B");
  ASTNode i = bv("i", 0), j = bv("j", 0);
  ASTNode e1 = bv("e1", 1), e2 = bv("e2", 2);
  ASTNode w1 = write(A, i, e1);
  ASTNode w2 = write(B, j, e2);
  ASTNode eqW = eqEdge(w1, w2, "eqW", true);
  ASTNode lam = bv("z_lam_eqW", 1);
  ASTNode wL = bv("z_wL_eqW", 0), wR = bv("z_wR_eqW", 0);
  witness(eqW, lam, wL, wR);

  // seed order: w1, w2, z_wL_eqW, z_wR_eqW
  size_t aw1 = writeAccess(w1);
  size_t aw2 = writeAccess(w2);
  readAccess(w1, lam, wL);
  readAccess(w2, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 2},
                  {"insertions", 6},
                  {"propagations", 2},
                  {"rule_D_WRITE", 2},
                  {"seeds", 4},
                  {"skipped_represented", 2},
                  {"skipped_seen", 2}});
  EXPECT_EQ(2u, r.conflicts.size());

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(w2, c.commonArray);
  EXPECT_EQ(aw2, c.leftAccess);
  EXPECT_EQ(aw1, c.rightAccess);
  EXPECT_TRUE(hasEqGuard(c.abstractPremise, j, i));
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, eqW));
  EXPECT_EQ(2u, c.abstractPremise.size());
  EXPECT_EQ(e2, c.abstractConclusionA);
  EXPECT_EQ(e1, c.abstractConclusionB);
}

// Section 11.2: an access arriving with the same concrete index and
// the same concrete value as the representative already at the array
// is dropped without insertion, so it never propagates onward -- here
// the duplicate read never climbs the write stacked on A.
TEST_F(ExtFixtureTest, RepresentedDuplicateIsPruned)
{
  ASTNode A = arr("A");
  ASTNode i = bv("i", 1), j = bv("j", 1); // concretely equal indices
  ASTNode x = bv("x", 2);
  ASTNode e = bv("e", 2);
  ASTNode w = write(A, x, e);
  ASTNode r1 = bv("r1", 3), r2 = bv("r2", 3); // concretely equal values

  size_t a1 = readAccess(A, i, r1);
  size_t a2 = readAccess(A, j, r2);
  size_t aw = writeAccess(w);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONSISTENT, r.status);
  // a1 seeds at A and climbs the write; a2 is represented by a1 at A
  // and goes nowhere; the write access stays at its own node.
  expectStats(r, {{"insertions", 3},
                  {"propagations", 1},
                  {"rule_U_WRITE", 1},
                  {"seeds", 2},
                  {"skipped_represented", 1},
                  {"skipped_seen", 1}});
  expectEvents(r, {{ExtEvent::SEED, "I_READ", A, (int)a1},
                   {ExtEvent::SKIP_REPRESENTED, "I_READ", A, (int)a2},
                   {ExtEvent::SEED, "I_WRITE", w, (int)aw},
                   {ExtEvent::PROPAGATE, "U_WRITE", w, (int)a1},
                   {ExtEvent::SKIP_SEEN, "D_WRITE", A, (int)a1}});
  // The observed contents carry the representative's pair once.
  ASSERT_EQ(1u, r.observed.count(A));
  ASSERT_EQ(1u, r.observed.find(A)->second.size());
  EXPECT_EQ(c2(1), r.observed.find(A)->second[0].first);
  EXPECT_EQ(c2(3), r.observed.find(A)->second[0].second);
}

// A pruned duplicate leaves congruence checking to its representative:
// a later access at the same concrete index with a different value
// conflicts against the representative, and the lemma premise is the
// index equality of exactly those two accesses.
TEST_F(ExtFixtureTest, ConflictFiresAgainstRepresentative)
{
  ASTNode A = arr("A");
  ASTNode i = bv("i", 1), j = bv("j", 1), k = bv("k", 1);
  ASTNode r1 = bv("r1", 3), r2 = bv("r2", 3), r3 = bv("r3", 2);

  size_t a1 = readAccess(A, i, r1);
  readAccess(A, j, r2); // represented by a1, dropped
  size_t a3 = readAccess(A, k, r3);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 1},
                  {"insertions", 1},
                  {"seeds", 1},
                  {"skipped_represented", 1}});

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(A, c.commonArray);
  EXPECT_EQ(a1, c.leftAccess);
  EXPECT_EQ(a3, c.rightAccess);
  EXPECT_EQ(c2(1), c.indexValue);
  EXPECT_EQ(c2(3), c.leftValue);
  EXPECT_EQ(c2(2), c.rightValue);
  ASSERT_EQ(1u, c.abstractPremise.size());
  EXPECT_EQ(ExtLemmaAtom::BV_EQ, c.abstractPremise[0].op);
  EXPECT_EQ(i, c.abstractPremise[0].a);
  EXPECT_EQ(k, c.abstractPremise[0].b);
  EXPECT_EQ(r1, c.abstractConclusionA);
  EXPECT_EQ(r3, c.abstractConclusionB);
}

// A conflict carries the lemma twice: the refinement form over
// abstraction names, and the theory-level form over the original
// terms -- the compound index term, the read terms themselves as the
// conclusion, and the crossed array equality as an atom of its own.
// The accesses are built by hand so the two layers hold different
// nodes, as in production, where an access's value term is the
// genuine read and its value name the read-abstraction symbol.
TEST_F(ExtFixtureTest, ConflictCarriesTheoryLemmaOverOriginalTerms)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode A = arr("A"), B = arr("B");
  ASTNode p = mgr.CreateSymbol("p", 0, 2);
  ASTNode iTerm = hf->CreateTerm(BVPLUS, 2, p, c2(1));
  ASTNode iName = bv("n_i", 0);
  ASTNode j = bv("j", 0); // a plain symbolic index names itself
  ASTNode rA = bv("rA", 1), rB = bv("rB", 2);
  ASTNode readA = hf->CreateTerm(READ, 2, A, iTerm);
  ASTNode readB = hf->CreateTerm(READ, 2, B, j);
  ASTNode eqAB = eqEdge(A, B, "eqAB", true);
  ASTNode lam = bv("z_lam_eqAB", 3);
  ASTNode wL = bv("z_wL_eqAB", 0), wR = bv("z_wR_eqAB", 0);
  witness(eqAB, lam, wL, wR);

  ExtAccess onA;
  onA.id = g.accesses.size();
  onA.isWrite = false;
  onA.site = A;
  onA.indexTerm = iTerm;
  onA.valueTerm = readA;
  onA.indexName = iName;
  onA.valueName = rA;
  g.accesses.push_back(onA);
  ExtAccess onB;
  onB.id = g.accesses.size();
  onB.isWrite = false;
  onB.site = B;
  onB.indexTerm = j;
  onB.valueTerm = readB;
  onB.indexName = j;
  onB.valueName = rB;
  g.accesses.push_back(onB);
  readAccess(A, lam, wL);
  readAccess(B, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);

  const ExtConflict& c = r.conflict;
  EXPECT_EQ(B, c.commonArray);
  EXPECT_EQ(onB.id, c.leftAccess);
  EXPECT_EQ(onA.id, c.rightAccess);

  // abstract layer: scalar names and the proxy literal
  ASSERT_EQ(2u, c.abstractPremise.size());
  EXPECT_TRUE(hasEqGuard(c.abstractPremise, j, iName));
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, eqAB));
  EXPECT_EQ(rB, c.abstractConclusionA);
  EXPECT_EQ(rA, c.abstractConclusionB);

  // theory layer: the original index term, the equality itself as an
  // atom carrying its record id, and the read terms as the conclusion
  ASSERT_EQ(2u, c.theoryPremise.size());
  EXPECT_TRUE(hasEqGuard(c.theoryPremise, j, iTerm));
  EXPECT_TRUE(hasArrayEqGuard(c.theoryPremise, A, B));
  for (size_t x = 0; x < c.theoryPremise.size(); x++)
  {
    if (c.theoryPremise[x].op == ExtLemmaAtom::ARRAY_EQ)
    {
      EXPECT_EQ(0u, c.theoryPremise[x].eqRecord);
    }
  }
  EXPECT_EQ(readB, c.theoryConclusionA);
  EXPECT_EQ(readA, c.theoryConclusionB);
}

// The shortest-path property of section 11.1: because rule I seeds
// every access before the fixed point starts and the work list is
// FIFO, discovery is breadth-first per access, and a conflict always
// fires at an access's first -- shortest -- arrival. The lemma premise
// therefore uses shortest propagation paths without the separate
// post-conflict BFS the paper describes (needed there because the
// paper's working list is a stack, i.e. depth-first). This test pins the
// property: two accesses can meet through a 2-edge route or a 4-edge
// route, with the equality adjacency ordered so that a depth-first
// work list would drive the resident access down the long route first
// and produce a 5-atom premise; breadth-first order must produce
// exactly the 3-atom premise of the short route.
TEST_F(ExtFixtureTest, ConflictPremiseUsesShortestPaths)
{
  ASTNode S = arr("S"), A = arr("A"), T = arr("T");
  ASTNode B1 = arr("B1"), B2 = arr("B2"), B3 = arr("B3");
  ASTNode iX = bv("iX", 1), iT = bv("iT", 1);
  ASTNode rX = bv("rX", 2), rT = bv("rT", 3);

  // Short route S - A - T; long route S - B1 - B2 - B3 - T. The two
  // T-incident edges are created so that the A edge precedes the B3
  // edge in T's adjacency.
  ASTNode e0 = eqEdge(S, A, "e0", true);
  eqEdge(S, B1, "e1", true);
  eqEdge(B1, B2, "e2", true);
  eqEdge(B2, B3, "e3", true);
  ASTNode e4 = eqEdge(A, T, "e4", true);
  eqEdge(B3, T, "e5", true);

  size_t aX = readAccess(S, iX, rX);
  size_t aT = readAccess(T, iT, rT);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);

  const ExtConflict& c = r.conflict;
  // aX reaches A at distance 1 before aT's expansion begins; aT then
  // meets it at A via its own 1-edge route.
  EXPECT_EQ(A, c.commonArray);
  EXPECT_EQ(aX, c.leftAccess);
  EXPECT_EQ(aT, c.rightAccess);
  ASSERT_EQ(1u, c.leftGuards.size());
  ASSERT_EQ(1u, c.rightGuards.size());

  // Premise: iX = iT plus the two short-route equalities, nothing from
  // the long route.
  ASSERT_EQ(3u, c.abstractPremise.size());
  EXPECT_TRUE(hasEqGuard(c.abstractPremise, iX, iT));
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, e0));
  EXPECT_TRUE(hasProxyGuard(c.abstractPremise, e4));
  EXPECT_EQ(rX, c.abstractConclusionA);
  EXPECT_EQ(rT, c.abstractConclusionB);
}

// Direct tests for the solve-time preparation layer: recovering the
// canonical equality operands from the witness anchors, computing the
// cone, eliminating array-valued if-then-else with its persistent
// replacement cache, scalar naming, and the loud failure when an
// anchor is missing. These drive ExtensionalityContext directly,
// without SAT or the array transformer, so a regression in
// preparation fails here instead of as a distant fatal error inside a
// full solve.
class ExtPrepareTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  ExtensionalityContext* ext;

  ExtPrepareTest()
  {
    mgr.UserFlags.enable_array_equality = true;
    ext = mgr.getExtensionality();
  }

  ASTNode arr(const char* name) { return mgr.CreateSymbol(name, 2, 2); }
  ASTNode bv(const char* name) { return mgr.CreateSymbol(name, 0, 2); }
};

TEST_F(ExtPrepareTest, RecoversOperandsConeAndNames)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b");
  ASTNode i = bv("i"), e = bv("e");
  // A compound write index, so preparation must give it a scalar name.
  ASTNode idx = hf->CreateTerm(BVPLUS, 2, i, mgr.CreateBVConst(2, 1));
  ASTNode w = hf->CreateArrayTerm(WRITE, 2, 2, {a, idx, e});

  ASTNode proxy = ext->makeEquality(w, b);
  ASSERT_EQ(SYMBOL, proxy.GetKind());
  ASSERT_EQ(1u, ext->getRecords().size());

  ext->beginSolve();
  ASTNode root = ext->conjoinRecordConstraints(proxy);
  ext->prepare(root);

  // Nothing rewrote the formula between construction and preparation,
  // so anchor recovery must reproduce the construction operands
  // exactly.
  const ExtensionalityContext::Record& r = ext->getRecords()[0];
  EXPECT_EQ(r.constructionLeft, r.canonicalLeft);
  EXPECT_EQ(r.constructionRight, r.canonicalRight);

  // The cone contains the operands and closes through the write to
  // its base.
  EXPECT_TRUE(ext->coneFrozen());
  EXPECT_TRUE(ext->inCone(w));
  EXPECT_TRUE(ext->inCone(b));
  EXPECT_TRUE(ext->inCone(a));

  // The compound index received a protected scalar name bound to it.
  bool namedIdx = false;
  const std::map<ASTNode, ASTNode>& n2t = ext->getNameToTerm();
  for (std::map<ASTNode, ASTNode>::const_iterator it = n2t.begin();
       it != n2t.end(); ++it)
  {
    EXPECT_TRUE(ext->isProtected(it->first));
    if (it->second == idx)
      namedIdx = true;
  }
  EXPECT_TRUE(namedIdx);
}

TEST_F(ExtPrepareTest, ArrayIteIsEliminatedWhenTheRegistryIsConjoined)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), d = arr("d");
  ASTNode c = mgr.CreateSymbol("c", 0, 0);

  // Building an array-valued if-then-else builds one, and moves no
  // solver state: at this point nobody can know whether the decision
  // procedure will run at all, so there is nothing to decide yet.
  ASTNode ite = hf->CreateArrayTerm(ITE, 2, 2, {c, a, b});
  EXPECT_EQ(ITE, ite.GetKind());
  EXPECT_EQ(0u, ext->getRecords().size());

  // An equality over it is one ordinary record. Its operand is the
  // if-then-else, so it is the anchor equations that mention it, not
  // the user's formula -- which is why the elimination has to run on
  // the conjunction rather than on the input alone.
  ASTNode proxy = ext->makeEquality(ite, d);
  ASSERT_EQ(1u, ext->getRecords().size());

  // Conjoining the registry's constraints is where section 4.1 runs.
  ext->beginSolve();
  ext->prepare(ext->conjoinRecordConstraints(proxy));
  ASSERT_EQ(3u, ext->getRecords().size()); // the user's, plus two guards
  EXPECT_TRUE(ext->inCone(a));
  EXPECT_TRUE(ext->inCone(b));

  // The operand the user's equality now stands over is the replacement:
  // a fresh array symbol of the same sort, in the cone.
  const ExtensionalityContext::Record& r = ext->getRecords()[0];
  const ASTNode repl =
      (r.canonicalLeft == d) ? r.canonicalRight : r.canonicalLeft;
  EXPECT_EQ(SYMBOL, repl.GetKind());
  EXPECT_EQ(2u, repl.GetIndexWidth());
  EXPECT_EQ(2u, repl.GetValueWidth());
  EXPECT_TRUE(ext->inCone(repl));

  // A second solve reuses the replacement and its two records instead
  // of minting a generation per solve. The lookup can be trusted
  // because it is keyed on the if-then-else the caller built, and the
  // elimination runs before any pass that could rewrite it.
  ext->beginSolve();
  ext->prepare(ext->conjoinRecordConstraints(proxy));
  EXPECT_EQ(3u, ext->getRecords().size());
}

TEST_F(ExtPrepareTest, NoArrayIteReachesPreprocessing)
{
  // The simplifier pushes a read through an array if-then-else, which
  // would leave a witness anchor as ite(c, read(a,l), read(b,l)) for
  // preparation to reconstruct the operand from -- and reconstructing
  // an operand out of an already-rewritten formula is what lost the
  // guards on a second solve and leaked a replacement per solve when
  // the condition had been normalised.
  //
  // It cannot arise, and this is the reason: the formula handed on to
  // preprocessing has no array if-then-else in it, so there is nothing
  // for a read to be pushed through. Checked over the whole DAG, not
  // just the anchors, since a survivor anywhere would reach the
  // simplifier.
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), d = arr("d");
  ASTNode c = mgr.CreateSymbol("c", 0, 0);

  ASTNode ite = hf->CreateArrayTerm(ITE, 2, 2, {c, a, b});
  ASTNode proxy = ext->makeEquality(ite, d);

  ext->beginSolve();
  const ASTNode toPreprocess = ext->conjoinRecordConstraints(proxy);

  std::set<ASTNode> seen;
  std::vector<ASTNode> todo(1, toPreprocess);
  while (!todo.empty())
  {
    const ASTNode n = todo.back();
    todo.pop_back();
    if (!seen.insert(n).second)
      continue;
    EXPECT_FALSE(n.GetKind() == ITE && n.GetIndexWidth() > 0)
        << "an array if-then-else survived into preprocessing";
    for (unsigned k = 0; k < n.Degree(); k++)
      todo.push_back(n[k]);
  }

  ext->prepare(toPreprocess);
  EXPECT_TRUE(ext->inCone(a));
  EXPECT_TRUE(ext->inCone(b));
}

TEST_F(ExtPrepareTest, MissingAnchorFailsLoudly)
{
  ASTNode a = arr("a"), b = arr("b");
  ASTNode proxy = ext->makeEquality(a, b);
  ext->beginSolve();
  // The record constraints are deliberately not conjoined: operand
  // recovery must refuse to guess.
  EXPECT_DEATH(ext->prepare(proxy),
               "witness-read defining equation was lost");
}

// The other recovery refusal: the anchor still holds a read, but at
// an index that is not this record's witness index. Witness indices
// are protected from substitution, so the shape is unreachable in a
// correct solve -- and must stay a loud error, never a guessed
// operand.
TEST_F(ExtPrepareTest, RewrittenWitnessIndexFailsLoudly)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b");
  ASTNode mu = bv("mu");
  ASTNode proxy = ext->makeEquality(a, b);
  (void)proxy;
  ASSERT_EQ(1u, ext->getRecords().size());
  const ExtensionalityContext::Record r = ext->getRecords()[0];

  ext->beginSolve();
  // The left anchor's witness read rebuilt over a foreign index; the
  // rest of the bundle intact.
  ASTNode badRead = hf->CreateTerm(READ, 2, r.constructionLeft, mu);
  ASTVec conjuncts;
  conjuncts.push_back(hf->CreateNode(EQ, r.nameL, badRead));
  conjuncts.push_back(r.anchorR);
  conjuncts.push_back(r.witnessClause);
  EXPECT_DEATH(ext->prepare(hf->CreateNode(AND, conjuncts)),
               "witness read's index was rewritten away");
}

// Operand recovery walks the whole DAG for equations of the anchor's
// shape and keeps what it finds in a hash-ordered container. Exactly
// one such equation may exist per witness name -- the names are fresh,
// substitution cannot move them and unconstrained removal cannot delete
// them -- but that is a property of the passes in between, not of this
// walk. A second one would otherwise be resolved by hash order, giving
// a different equality operand from run to run.
TEST_F(ExtPrepareTest, DuplicateAnchorFailsLoudly)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), c = arr("c");
  ASTNode proxy = ext->makeEquality(a, b);
  (void)proxy;
  ASSERT_EQ(1u, ext->getRecords().size());
  const ExtensionalityContext::Record r = ext->getRecords()[0];

  ext->beginSolve();
  // The intact bundle, plus a rival equation of the same shape for the
  // same name over a different array.
  ASTVec conjuncts;
  conjuncts.push_back(r.anchorL);
  conjuncts.push_back(r.anchorR);
  conjuncts.push_back(r.witnessClause);
  conjuncts.push_back(
      hf->CreateNode(EQ, r.nameL, hf->CreateTerm(READ, 2, c, r.lambda)));
  EXPECT_DEATH(ext->prepare(hf->CreateNode(AND, conjuncts)),
               "occurs twice with different right-hand sides");
}

// possibleConeSymbols is collected from the operands as they were
// built, and decides which reads are protected from the
// read-equals-constant substitution; the cone is closed over the
// operands as they are after simplification. If a pass ever rewrites an
// operand to name an array symbol that was not under it before, that
// symbol's reads were never protected, and an observation the
// consistency check depends on may already have been substituted away.
TEST_F(ExtPrepareTest, UnanticipatedConeSymbolFailsLoudly)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), z = arr("z");
  ASTNode proxy = ext->makeEquality(a, b);
  (void)proxy;
  ASSERT_EQ(1u, ext->getRecords().size());
  const ExtensionalityContext::Record r = ext->getRecords()[0];

  ext->beginSolve();
  // Stands in for a pass that rewrote the left operand into a term over
  // z, an array the registry never saw when the equality was built.
  ASTVec conjuncts;
  conjuncts.push_back(
      hf->CreateNode(EQ, r.nameL, hf->CreateTerm(READ, 2, z, r.lambda)));
  conjuncts.push_back(r.anchorR);
  conjuncts.push_back(r.witnessClause);
  EXPECT_DEATH(ext->prepare(hf->CreateNode(AND, conjuncts)),
               "entered the cone that was not anticipated");
}

// The decision table combining STP's own model evaluation with the
// array consistency check: an array conflict always takes priority
// (only its lemma can rule the candidate out), and a candidate is
// satisfiable only when both checks pass. All twenty cells.
TEST(ExtCertification, TruthTable)
{
  typedef ExtensionalityContext EC;
  // registry empty: EXTCHK skipped; ordinary result decides. (A
  // consistent verdict without a registry is tolerated identically;
  // conflict, witness trouble or a name divergence from a checker
  // that had nothing to check is an internal error.)
  EXPECT_EQ(EC::RETURN_SAT,
            EC::decideCertification(true, false, EC::EXT_SKIPPED));
  EXPECT_EQ(EC::RUN_HOST_REFINEMENT,
            EC::decideCertification(false, false, EC::EXT_SKIPPED));
  EXPECT_EQ(EC::RETURN_SAT,
            EC::decideCertification(true, false, EC::EXT_CONSISTENT));
  EXPECT_EQ(EC::RUN_HOST_REFINEMENT,
            EC::decideCertification(false, false, EC::EXT_CONSISTENT));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(true, false, EC::EXT_CONFLICT));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(false, false, EC::EXT_CONFLICT));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(true, false, EC::EXT_WITNESS_ERROR));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(false, false, EC::EXT_WITNESS_ERROR));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(true, false, EC::EXT_NAME_DIVERGENCE));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(false, false, EC::EXT_NAME_DIVERGENCE));

  // registry nonempty: EXTCHK conflict has priority over both ordinary
  // results; SAT only for ordinary-true + consistent; a skipped check
  // despite a nonempty registry is an internal error whatever the
  // ordinary result was, since cone reads are exempt from ordinary
  // refinement and only the checker polices them. A name divergence
  // hands the candidate to the host's read refinement in both cases:
  // it is neither certifiable nor refutable by an array lemma, and the
  // missing link is an ordinary read-congruence axiom.
  EXPECT_EQ(EC::RETURN_SAT,
            EC::decideCertification(true, true, EC::EXT_CONSISTENT));
  EXPECT_EQ(EC::ADD_EXT_LEMMA,
            EC::decideCertification(true, true, EC::EXT_CONFLICT));
  EXPECT_EQ(EC::RUN_HOST_REFINEMENT,
            EC::decideCertification(false, true, EC::EXT_CONSISTENT));
  EXPECT_EQ(EC::ADD_EXT_LEMMA,
            EC::decideCertification(false, true, EC::EXT_CONFLICT));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(true, true, EC::EXT_WITNESS_ERROR));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(false, true, EC::EXT_WITNESS_ERROR));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(true, true, EC::EXT_SKIPPED));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(false, true, EC::EXT_SKIPPED));
  EXPECT_EQ(EC::RUN_HOST_REFINEMENT,
            EC::decideCertification(true, true, EC::EXT_NAME_DIVERGENCE));
  EXPECT_EQ(EC::RUN_HOST_REFINEMENT,
            EC::decideCertification(false, true, EC::EXT_NAME_DIVERGENCE));
}

} // namespace

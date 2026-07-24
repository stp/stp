/***********
AUTHORS: Andrew V. Jones

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

  void expectStats(const ExtCheckResult& r,
                   const std::map<std::string, int>& expected)
  {
    EXPECT_EQ(expected, r.stats);
  }

  void expectEvents(const ExtCheckResult& r,
                    const std::vector<ExpectedEvent>& expected)
  {
    ASSERT_EQ(expected.size(), r.events.size());
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
  EXPECT_EQ(1u, r.observed.find(A)->second.size());
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

  // reference seed order: r1, r2, w1, w2, w3
  size_t ar1 = readAccess(w2, i, r1);
  size_t ar2 = readAccess(w3, k, r2);
  size_t aw1 = writeAccess(w1);
  size_t aw2 = writeAccess(w2);
  size_t aw3 = writeAccess(w3);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 1},
                  {"insertions", 8},
                  {"propagations", 3},
                  {"rule_D_WRITE", 2},
                  {"rule_U_WRITE", 1},
                  {"seeds", 5}});
  expectEvents(r, {{ExtEvent::SEED, "I_READ", w2, (int)ar1},
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

  // reference seed order: rA, rB, z_wL_eqAB, z_wR_eqAB
  size_t aA = readAccess(A, i, rA);
  size_t aB = readAccess(B, j, rB);
  readAccess(A, lam, wL);
  readAccess(B, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 1}, {"insertions", 4}, {"seeds", 4}});

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
  EXPECT_STREQ("R_EQ", r.events.back().rule);
  EXPECT_EQ(ExtEvent::CONFLICT, r.events.back().kind);
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

  // reference seed order: r1, r2, w1, w2, z_wL_eqW, z_wR_eqW
  readAccess(A, i1, r1);
  readAccess(A, i2, r2);
  size_t aw1 = writeAccess(w1);
  size_t aw2 = writeAccess(w2);
  readAccess(w1, lam, wL);
  readAccess(w2, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 1}, {"insertions", 6}, {"seeds", 6}});

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

  // reference seed order: r1, w1, w2
  size_t ar1 = readAccess(w2, i, r1);
  size_t aw1 = writeAccess(w1);
  writeAccess(w2);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 1}, {"insertions", 3}, {"seeds", 3}});

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

// Two chained true equalities a = b and b = c: the work list must
// carry an access across both edges to meet its counterpart.
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

  // reference seed order: rA, rC, z_wL_eqAB, z_wL_eqBC, z_wR_eqAB, z_wR_eqBC
  size_t aA = readAccess(A, i, rA);
  size_t aC = readAccess(C, j, rC);
  readAccess(A, lamAB, wLAB);
  readAccess(B, lamBC, wLBC);
  readAccess(B, lamAB, wRAB);
  readAccess(C, lamBC, wRBC);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 1},
                  {"insertions", 7},
                  {"propagations", 1},
                  {"rule_R_EQ", 1},
                  {"seeds", 6}});

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

  // reference seed order: rA, rB, w1, w2, z_wL_eqW, z_wR_eqW
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
  expectStats(r, {{"conflicts", 1},
                  {"insertions", 12},
                  {"propagations", 6},
                  {"rule_D_WRITE", 2},
                  {"rule_L_EQ", 1},
                  {"rule_R_EQ", 1},
                  {"rule_U_WRITE", 2},
                  {"seeds", 6},
                  {"skipped_represented", 2},
                  {"skipped_seen", 1}});
  expectEvents(r, {{ExtEvent::SEED, "I_READ", A, (int)aA},
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

  // reference seed order: w1, w2, z_wL_eqW, z_wR_eqW
  size_t aw1 = writeAccess(w1);
  size_t aw2 = writeAccess(w2);
  readAccess(w1, lam, wL);
  readAccess(w2, lam, wR);

  ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
  expectStats(r, {{"conflicts", 1}, {"insertions", 4}, {"seeds", 4}});

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

// The decision table combining STP's own model evaluation with the
// array consistency check: an array conflict always takes priority
// (only its lemma can rule the candidate out), and a candidate is
// satisfiable only when both checks pass.
TEST(ExtCertification, TruthTable)
{
  typedef ExtensionalityContext EC;
  // registry empty: EXTCHK skipped; ordinary result decides
  EXPECT_EQ(EC::RETURN_SAT,
            EC::decideCertification(true, false, EC::EXT_SKIPPED));
  EXPECT_EQ(EC::RUN_HOST_REFINEMENT,
            EC::decideCertification(false, false, EC::EXT_SKIPPED));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(true, false, EC::EXT_CONFLICT));
  EXPECT_EQ(EC::INTERNAL_ERROR,
            EC::decideCertification(false, false, EC::EXT_WITNESS_ERROR));

  // registry nonempty: EXTCHK conflict has priority over both ordinary
  // results; SAT only for ordinary-true + consistent.
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
}

} // namespace

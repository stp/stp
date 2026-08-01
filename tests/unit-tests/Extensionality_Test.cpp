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
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <map>
#include <sstream>

using namespace stp;

namespace
{

TEST(ArrayEqualityAstTest, OpaqueNodeIsTypedHashedAndPrintedAsEquality)
{
  STPMgr mgr;
  mgr.UserFlags.enable_array_equality = true;
  NodeFactory* hf = mgr.hashingNodeFactory;
  const ASTNode a = mgr.CreateSymbol("a", 2, 3);
  const ASTNode b = mgr.CreateSymbol("b", 2, 3);

  const ASTNode eq = hf->CreateNode(EQ, a, b);
  EXPECT_EQ(ARRAY_EQ, eq.GetKind());
  EXPECT_EQ(eq, hf->CreateNode(EQ, b, a));
  EXPECT_TRUE(eq.isPred());
  EXPECT_TRUE(isAtomic(eq.GetKind()));
  EXPECT_TRUE(BVTypeCheck(eq));

  SimplifyingNodeFactory simplifying(*mgr.hashingNodeFactory, mgr);
  EXPECT_EQ(mgr.ASTTrue, simplifying.CreateNode(EQ, ASTVec{a, a}));

  std::ostringstream out;
  printer::SMTLIB2_Print1(out, eq, 0, false);
  EXPECT_EQ("(= |a| |b|)", out.str());
}

TEST(ArrayEqualityAstTest, FunctionApplicationSpecializesOpaqueOperands)
{
  STPMgr mgr;
  SimplifyingNodeFactory simplifying(*mgr.hashingNodeFactory, mgr);
  Cpp_interface interface(mgr, &simplifying);
  NodeFactory* hf = mgr.hashingNodeFactory;

  const ASTNode a = mgr.CreateSymbol("a", 1, 1);
  const ASTNode b = mgr.CreateSymbol("b", 1, 1);
  const ASTNode formal = mgr.CreateSymbol("i", 0, 1);
  const ASTNode one = mgr.CreateOneConst(1);
  const ASTNode body = hf->CreateNode(
      ARRAY_EQ, hf->CreateArrayTerm(WRITE, 1, 1, a, formal, one), b);

  interface.storeFunction("f", ASTVec{formal}, body);

  const ASTNode zero = mgr.CreateZeroConst(1);
  const ASTNode atZero = interface.applyFunction("f", ASTVec{zero});
  const ASTNode atOne = interface.applyFunction("f", ASTVec{one});
  const ASTNode expectedZero = hf->CreateNode(
      ARRAY_EQ, hf->CreateArrayTerm(WRITE, 1, 1, a, zero, one), b);
  const ASTNode expectedOne = hf->CreateNode(
      ARRAY_EQ, hf->CreateArrayTerm(WRITE, 1, 1, a, one, one), b);

  EXPECT_EQ(expectedZero, atZero);
  EXPECT_EQ(expectedOne, atOne);
  EXPECT_NE(atZero, atOne);
  EXPECT_EQ(ARRAY_EQ, atZero.GetKind());
  EXPECT_EQ(ARRAY_EQ, atOne.GetKind());
}

TEST(ArrayEqualityAstTest, ActivationIsTheTransitiveClosureOfCurrentRoot)
{
  STPMgr mgr;
  mgr.UserFlags.enable_array_equality = true;
  ExtensionalityContext ext(&mgr);
  NodeFactory* hf = mgr.hashingNodeFactory;

  const ASTNode a = mgr.CreateSymbol("a", 1, 1);
  const ASTNode b = mgr.CreateSymbol("b", 1, 1);
  const ASTNode c = mgr.CreateSymbol("c", 1, 1);
  const ASTNode d = mgr.CreateSymbol("d", 1, 1);
  const ASTNode e = mgr.CreateSymbol("e", 1, 1);
  const ASTNode f = mgr.CreateSymbol("f", 1, 1);
  const ASTNode g = mgr.CreateSymbol("g", 1, 1);

  const ASTNode dormant = hf->CreateNode(EQ, f, g);
  ext.beginSolve();
  ext.lowerArrayEqualities(dormant);
  ASSERT_EQ(1u, ext.getActiveRecordCount());

  const ASTNode inner = hf->CreateNode(EQ, a, b);
  const ASTNode choice =
      hf->CreateArrayTerm(ITE, 1, 1, inner, c, d);
  const ASTNode outer = hf->CreateNode(EQ, choice, e);

  ext.beginSolve();
  const ASTNode lowered = ext.lowerArrayEqualities(outer);
  ASSERT_EQ(2u, ext.getActiveRecordCount());
  ASSERT_EQ(2u, ext.getRecords().size());
  ASSERT_EQ(SYMBOL, lowered.GetKind());

  // The outer record hides its operand graph behind one proxy. Activation
  // must nevertheless follow that operand and discover the inner proxy used
  // as the reconstructed ITE condition.
  const ExtensionalityContext::Record* outerRecord = nullptr;
  for (const ExtensionalityContext::Record& r : ext.getRecords())
    if (r.proxy == lowered)
      outerRecord = &r;
  ASSERT_NE(nullptr, outerRecord);
  const ASTNode choiceOperand =
      outerRecord->constructionLeft.GetKind() == ITE
          ? outerRecord->constructionLeft
          : outerRecord->constructionRight;
  ASSERT_EQ(ITE, choiceOperand.GetKind());
  EXPECT_EQ(SYMBOL, choiceOperand[0].GetKind());

  const ASTNode constrained = ext.conjoinRecordConstraints(lowered);
  ASTNodeSet visited;
  ASTVec pending(1, constrained);
  while (!pending.empty())
  {
    const ASTNode n = pending.back();
    pending.pop_back();
    if (!visited.insert(n).second)
      continue;
    EXPECT_NE(ARRAY_EQ, n.GetKind());
    for (unsigned i = 0; i < n.Degree(); ++i)
      pending.push_back(n[i]);
  }

  ext.beginSolve();
  ext.lowerArrayEqualities(mgr.ASTTrue);
  EXPECT_EQ(0u, ext.getActiveRecordCount());
  EXPECT_EQ(0u, ext.getRecords().size());

  ext.beginSolve();
  ext.lowerArrayEqualities(dormant);
  EXPECT_EQ(1u, ext.getActiveRecordCount());
  EXPECT_EQ(1u, ext.getRecords().size());
}

TEST(ExtGuardTest, PathPayloadRemainsCompact)
{
  // A predecessor entry stores exactly one guard. Keep its payload below the
  // old 96-byte variant-specific representation.
  EXPECT_LE(sizeof(ExtGuard), 64u);
}

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

// An independent finite-semantics oracle for the complete checker. With
// one-bit indexes and one-bit elements, an array has only four possible
// interpretations, so every candidate assignment can be compared against
// every genuine array model. The oracle below deliberately does not walk an
// ExtGraph or reproduce I/D/U/R/L/T/C: each test evaluates its concrete
// READ/WRITE/ITE/equality expression directly.
class OneBitModel : public ExtModelView
{
public:
  std::map<ASTNode, ASTNode> bvVals;
  std::map<ASTNode, bool> boolVals;

  virtual ASTNode bvValue(const ASTNode& term)
  {
    if (term.GetKind() == BVCONST)
      return term;
    std::map<ASTNode, ASTNode>::const_iterator it = bvVals.find(term);
    if (it == bvVals.end())
      FatalError("OneBitModel: missing bv value", term);
    return it->second;
  }

  virtual bool boolValue(const ASTNode& term)
  {
    if (term.GetKind() == TRUE || term.GetKind() == FALSE)
      return term.GetKind() == TRUE;
    std::map<ASTNode, bool>::const_iterator it = boolVals.find(term);
    if (it == boolVals.end())
      FatalError("OneBitModel: missing bool value", term);
    return it->second;
  }
};

class ExtCheckerOneBitOracleTest : public ::testing::Test
{
protected:
  typedef unsigned ConcreteArray;

  STPMgr mgr;
  ExtGraph graph;
  OneBitModel model;
  size_t nextRecord = 0;

  static unsigned candidateBit(unsigned mask, unsigned position)
  {
    return (mask >> position) & 1u;
  }

  static unsigned readCell(ConcreteArray array, unsigned index)
  {
    return (array >> index) & 1u;
  }

  static ConcreteArray writeCell(ConcreteArray array, unsigned index,
                                 unsigned value)
  {
    return (array & ~(1u << index)) | (value << index);
  }

  ASTNode arraySymbol(const char* name)
  {
    return mgr.CreateSymbol(name, 1, 1);
  }

  ASTNode bitSymbol(const char* name)
  {
    return mgr.CreateSymbol(name, 0, 1);
  }

  ASTNode boolSymbol(const char* name)
  {
    return mgr.CreateSymbol(name, 0, 0);
  }

  ASTNode bitConstant(unsigned value)
  {
    return mgr.CreateBVConst(1, value);
  }

  void assignBit(const ASTNode& symbol, unsigned value)
  {
    model.bvVals[symbol] = bitConstant(value);
  }

  void assignBool(const ASTNode& symbol, bool value)
  {
    model.boolVals[symbol] = value;
  }

  ASTNode writeNode(const ASTNode& base, const ASTNode& index,
                    const ASTNode& value)
  {
    ASTNode write = mgr.hashingNodeFactory->CreateArrayTerm(
        WRITE, 1, 1, {base, index, value});
    ExtWriteNode info;
    info.write = write;
    info.base = base;
    info.indexTerm = index;
    info.indexName = index;
    graph.writes[write] = info;
    graph.writeParents[base].push_back(write);
    return write;
  }

  ASTNode iteNode(const ASTNode& condition, const ASTNode& thn,
                  const ASTNode& els)
  {
    ASTNode ite = mgr.hashingNodeFactory->CreateArrayTerm(
        ITE, 1, 1, {condition, thn, els});
    ExtIteNode info;
    info.ite = ite;
    info.condTerm = condition;
    info.condName = condition;
    info.thn = thn;
    info.els = els;
    graph.ites[ite] = info;
    graph.iteParents[thn].push_back(ite);
    if (els != thn)
      graph.iteParents[els].push_back(ite);
    return ite;
  }

  ASTNode equalityEdge(const ASTNode& left, const ASTNode& right,
                       const char* proxyName)
  {
    const ASTNode proxy = boolSymbol(proxyName);
    ExtEqEdge edge;
    edge.record = nextRecord++;
    edge.left = left;
    edge.right = right;
    edge.proxy = proxy;
    const size_t edgeIndex = graph.eqEdges.size();
    graph.eqEdges.push_back(edge);
    graph.eqAdjacency[left].push_back(edgeIndex);
    if (left != right)
      graph.eqAdjacency[right].push_back(edgeIndex);
    return proxy;
  }

  void witness(const ASTNode& proxy, const ASTNode& index,
               const ASTNode& leftValue, const ASTNode& rightValue)
  {
    ExtWitness obligation;
    obligation.record = graph.witnesses.size();
    obligation.proxy = proxy;
    obligation.index = index;
    obligation.leftValue = leftValue;
    obligation.rightValue = rightValue;
    graph.witnesses.push_back(obligation);
  }

  void readAccess(const ASTNode& array, const ASTNode& index,
                  const ASTNode& value)
  {
    ExtAccess access;
    access.id = graph.accesses.size();
    access.isWrite = false;
    access.site = array;
    access.indexTerm = index;
    access.valueTerm = value;
    access.indexName = index;
    access.valueName = value;
    graph.accesses.push_back(access);
  }

  void writeAccess(const ASTNode& write)
  {
    ExtAccess access;
    access.id = graph.accesses.size();
    access.isWrite = true;
    access.site = write;
    access.indexTerm = write[1];
    access.valueTerm = write[2];
    access.indexName = write[1];
    access.valueName = write[2];
    graph.accesses.push_back(access);
  }

  template <class AssignCandidate, class FiniteOracle>
  void compareEveryCandidate(const char* scenario, unsigned candidateBits,
                             AssignCandidate assignCandidate,
                             FiniteOracle finiteOracle)
  {
    const unsigned candidateCount = 1u << candidateBits;
    for (unsigned mask = 0; mask < candidateCount; ++mask)
    {
      SCOPED_TRACE(::testing::Message()
                   << scenario << " candidate mask " << mask);
      assignCandidate(mask);
      const ExtCheckResult result = ExtChecker::check(graph, model, false);
      const bool checkerAccepts = result.status == ExtCheckResult::CONSISTENT;
      EXPECT_EQ(finiteOracle(mask), checkerAccepts)
          << "checker status " << result.status;
    }
  }
};

TEST_F(ExtCheckerOneBitOracleTest, ReadMatchesFiniteDenotationalSemantics)
{
  const ASTNode array = arraySymbol("oracle_read_array");
  const ASTNode i = bitSymbol("oracle_read_i");
  const ASTNode j = bitSymbol("oracle_read_j");
  const ASTNode ri = bitSymbol("oracle_read_ri");
  const ASTNode rj = bitSymbol("oracle_read_rj");
  readAccess(array, i, ri);
  readAccess(array, j, rj);

  compareEveryCandidate(
      "READ", 4,
      [&](unsigned mask) {
        assignBit(i, candidateBit(mask, 0));
        assignBit(j, candidateBit(mask, 1));
        assignBit(ri, candidateBit(mask, 2));
        assignBit(rj, candidateBit(mask, 3));
      },
      [&](unsigned mask) {
        const unsigned indexI = candidateBit(mask, 0);
        const unsigned indexJ = candidateBit(mask, 1);
        const unsigned valueI = candidateBit(mask, 2);
        const unsigned valueJ = candidateBit(mask, 3);
        for (ConcreteArray concrete = 0; concrete < 4; ++concrete)
          if (readCell(concrete, indexI) == valueI &&
              readCell(concrete, indexJ) == valueJ)
            return true;
        return false;
      });
}

TEST_F(ExtCheckerOneBitOracleTest, WriteMatchesFiniteDenotationalSemantics)
{
  const ASTNode array = arraySymbol("oracle_write_array");
  const ASTNode writeIndex = bitSymbol("oracle_write_k");
  const ASTNode writeValue = bitSymbol("oracle_write_v");
  const ASTNode writeReadIndex = bitSymbol("oracle_write_i");
  const ASTNode writeReadValue = bitSymbol("oracle_write_rw");
  const ASTNode baseReadIndex = bitSymbol("oracle_write_j");
  const ASTNode baseReadValue = bitSymbol("oracle_write_ra");
  const ASTNode write = writeNode(array, writeIndex, writeValue);
  writeAccess(write);
  readAccess(write, writeReadIndex, writeReadValue);
  readAccess(array, baseReadIndex, baseReadValue);

  compareEveryCandidate(
      "WRITE", 6,
      [&](unsigned mask) {
        assignBit(writeIndex, candidateBit(mask, 0));
        assignBit(writeValue, candidateBit(mask, 1));
        assignBit(writeReadIndex, candidateBit(mask, 2));
        assignBit(writeReadValue, candidateBit(mask, 3));
        assignBit(baseReadIndex, candidateBit(mask, 4));
        assignBit(baseReadValue, candidateBit(mask, 5));
      },
      [&](unsigned mask) {
        const unsigned k = candidateBit(mask, 0);
        const unsigned v = candidateBit(mask, 1);
        const unsigned i = candidateBit(mask, 2);
        const unsigned rw = candidateBit(mask, 3);
        const unsigned j = candidateBit(mask, 4);
        const unsigned ra = candidateBit(mask, 5);
        for (ConcreteArray concrete = 0; concrete < 4; ++concrete)
        {
          const ConcreteArray updated = writeCell(concrete, k, v);
          if (readCell(updated, i) == rw && readCell(concrete, j) == ra)
            return true;
        }
        return false;
      });
}

TEST_F(ExtCheckerOneBitOracleTest,
       EqualityAndWitnessMatchFiniteDenotationalSemantics)
{
  const ASTNode left = arraySymbol("oracle_eq_left");
  const ASTNode right = arraySymbol("oracle_eq_right");
  const ASTNode proxy = equalityEdge(left, right, "oracle_eq_proxy");
  const ASTNode lambda = bitSymbol("oracle_eq_lambda");
  const ASTNode witnessLeft = bitSymbol("oracle_eq_witness_left");
  const ASTNode witnessRight = bitSymbol("oracle_eq_witness_right");
  const ASTNode i = bitSymbol("oracle_eq_i");
  const ASTNode readLeft = bitSymbol("oracle_eq_read_left");
  const ASTNode j = bitSymbol("oracle_eq_j");
  const ASTNode readRight = bitSymbol("oracle_eq_read_right");
  witness(proxy, lambda, witnessLeft, witnessRight);
  readAccess(left, lambda, witnessLeft);
  readAccess(right, lambda, witnessRight);
  readAccess(left, i, readLeft);
  readAccess(right, j, readRight);

  compareEveryCandidate(
      "EQUALITY", 8,
      [&](unsigned mask) {
        assignBool(proxy, candidateBit(mask, 0) != 0);
        assignBit(lambda, candidateBit(mask, 1));
        assignBit(witnessLeft, candidateBit(mask, 2));
        assignBit(witnessRight, candidateBit(mask, 3));
        assignBit(i, candidateBit(mask, 4));
        assignBit(readLeft, candidateBit(mask, 5));
        assignBit(j, candidateBit(mask, 6));
        assignBit(readRight, candidateBit(mask, 7));
      },
      [&](unsigned mask) {
        const bool proxyValue = candidateBit(mask, 0) != 0;
        const unsigned witnessIndex = candidateBit(mask, 1);
        const unsigned wl = candidateBit(mask, 2);
        const unsigned wr = candidateBit(mask, 3);
        const unsigned indexLeft = candidateBit(mask, 4);
        const unsigned valueLeft = candidateBit(mask, 5);
        const unsigned indexRight = candidateBit(mask, 6);
        const unsigned valueRight = candidateBit(mask, 7);
        for (ConcreteArray concreteLeft = 0; concreteLeft < 4;
             ++concreteLeft)
          for (ConcreteArray concreteRight = 0; concreteRight < 4;
               ++concreteRight)
            if (readCell(concreteLeft, witnessIndex) == wl &&
                readCell(concreteRight, witnessIndex) == wr &&
                readCell(concreteLeft, indexLeft) == valueLeft &&
                readCell(concreteRight, indexRight) == valueRight &&
                proxyValue == (concreteLeft == concreteRight) &&
                (proxyValue || wl != wr))
              return true;
        return false;
      });
}

TEST_F(ExtCheckerOneBitOracleTest, IteMatchesFiniteDenotationalSemantics)
{
  const ASTNode left = arraySymbol("oracle_ite_left");
  const ASTNode right = arraySymbol("oracle_ite_right");
  const ASTNode condition = boolSymbol("oracle_ite_condition");
  const ASTNode ite = iteNode(condition, left, right);
  const ASTNode i = bitSymbol("oracle_ite_i");
  const ASTNode readIte = bitSymbol("oracle_ite_read");
  const ASTNode j = bitSymbol("oracle_ite_j");
  const ASTNode readLeft = bitSymbol("oracle_ite_read_left");
  const ASTNode k = bitSymbol("oracle_ite_k");
  const ASTNode readRight = bitSymbol("oracle_ite_read_right");
  readAccess(ite, i, readIte);
  readAccess(left, j, readLeft);
  readAccess(right, k, readRight);

  compareEveryCandidate(
      "ITE", 7,
      [&](unsigned mask) {
        assignBool(condition, candidateBit(mask, 0) != 0);
        assignBit(i, candidateBit(mask, 1));
        assignBit(readIte, candidateBit(mask, 2));
        assignBit(j, candidateBit(mask, 3));
        assignBit(readLeft, candidateBit(mask, 4));
        assignBit(k, candidateBit(mask, 5));
        assignBit(readRight, candidateBit(mask, 6));
      },
      [&](unsigned mask) {
        const bool conditionValue = candidateBit(mask, 0) != 0;
        const unsigned iteIndex = candidateBit(mask, 1);
        const unsigned iteValue = candidateBit(mask, 2);
        const unsigned leftIndex = candidateBit(mask, 3);
        const unsigned leftValue = candidateBit(mask, 4);
        const unsigned rightIndex = candidateBit(mask, 5);
        const unsigned rightValue = candidateBit(mask, 6);
        for (ConcreteArray concreteLeft = 0; concreteLeft < 4;
             ++concreteLeft)
          for (ConcreteArray concreteRight = 0; concreteRight < 4;
               ++concreteRight)
          {
            const ConcreteArray selected =
                conditionValue ? concreteLeft : concreteRight;
            if (readCell(selected, iteIndex) == iteValue &&
                readCell(concreteLeft, leftIndex) == leftValue &&
                readCell(concreteRight, rightIndex) == rightValue)
              return true;
          }
        return false;
      });
}

TEST_F(ExtCheckerOneBitOracleTest,
       MixedGraphMatchesFiniteDenotationalSemantics)
{
  const ASTNode arrayA = arraySymbol("oracle_mixed_a");
  const ASTNode arrayB = arraySymbol("oracle_mixed_b");
  const ASTNode arrayC = arraySymbol("oracle_mixed_c");
  const ASTNode writeIndex = bitSymbol("oracle_mixed_k");
  const ASTNode writeValue = bitSymbol("oracle_mixed_v");
  const ASTNode write = writeNode(arrayA, writeIndex, writeValue);
  const ASTNode condition = boolSymbol("oracle_mixed_condition");
  const ASTNode ite = iteNode(condition, write, arrayB);
  const ASTNode proxy = equalityEdge(ite, arrayC, "oracle_mixed_proxy");
  const ASTNode lambda = bitSymbol("oracle_mixed_lambda");
  const ASTNode witnessIte = bitSymbol("oracle_mixed_witness_ite");
  const ASTNode witnessC = bitSymbol("oracle_mixed_witness_c");
  const ASTNode readAZero = bitSymbol("oracle_mixed_read_a_zero");
  const ASTNode readCOne = bitSymbol("oracle_mixed_read_c_one");
  const ASTNode zero = bitConstant(0);
  const ASTNode one = bitConstant(1);
  witness(proxy, lambda, witnessIte, witnessC);
  writeAccess(write);
  readAccess(ite, lambda, witnessIte);
  readAccess(arrayC, lambda, witnessC);
  readAccess(arrayA, zero, readAZero);
  readAccess(arrayC, one, readCOne);

  compareEveryCandidate(
      "MIXED", 9,
      [&](unsigned mask) {
        assignBit(writeIndex, candidateBit(mask, 0));
        assignBit(writeValue, candidateBit(mask, 1));
        assignBool(condition, candidateBit(mask, 2) != 0);
        assignBool(proxy, candidateBit(mask, 3) != 0);
        assignBit(lambda, candidateBit(mask, 4));
        assignBit(witnessIte, candidateBit(mask, 5));
        assignBit(witnessC, candidateBit(mask, 6));
        assignBit(readAZero, candidateBit(mask, 7));
        assignBit(readCOne, candidateBit(mask, 8));
      },
      [&](unsigned mask) {
        const unsigned k = candidateBit(mask, 0);
        const unsigned v = candidateBit(mask, 1);
        const bool conditionValue = candidateBit(mask, 2) != 0;
        const bool proxyValue = candidateBit(mask, 3) != 0;
        const unsigned witnessIndex = candidateBit(mask, 4);
        const unsigned witnessIteValue = candidateBit(mask, 5);
        const unsigned witnessCValue = candidateBit(mask, 6);
        const unsigned aZeroValue = candidateBit(mask, 7);
        const unsigned cOneValue = candidateBit(mask, 8);
        for (ConcreteArray concreteA = 0; concreteA < 4; ++concreteA)
          for (ConcreteArray concreteB = 0; concreteB < 4; ++concreteB)
            for (ConcreteArray concreteC = 0; concreteC < 4; ++concreteC)
            {
              const ConcreteArray updated = writeCell(concreteA, k, v);
              const ConcreteArray selected =
                  conditionValue ? updated : concreteB;
              if (readCell(selected, witnessIndex) == witnessIteValue &&
                  readCell(concreteC, witnessIndex) == witnessCValue &&
                  readCell(concreteA, 0) == aZeroValue &&
                  readCell(concreteC, 1) == cOneValue &&
                  proxyValue == (selected == concreteC) &&
                  (proxyValue || witnessIteValue != witnessCValue))
                return true;
            }
        return false;
      });
}

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

  ASTNode arrayIte(const ASTNode& condTerm, const ASTNode& condName,
                   const ASTNode& thn, const ASTNode& els)
  {
    NodeFactory* hf = mgr.hashingNodeFactory;
    ASTNode ite = hf->CreateArrayTerm(ITE, 2, 2,
                                      {condTerm, thn, els});
    ExtIteNode info;
    info.ite = ite;
    info.condTerm = condTerm;
    info.condName = condName;
    info.thn = thn;
    info.els = els;
    g.ites[ite] = info;
    g.iteParents[thn].push_back(ite);
    if (els != thn)
      g.iteParents[els].push_back(ite);
    return ite;
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
  static bool hasBoolGuard(const std::vector<ExtLemmaAtom>& premise,
                           const ASTNode& term, bool positive)
  {
    const ExtLemmaAtom::Op op = positive ? ExtLemmaAtom::BOOL_LIT
                                         : ExtLemmaAtom::BOOL_LIT_NEG;
    for (size_t i = 0; i < premise.size(); i++)
      if (premise[i].op == op && premise[i].boolTerm == term)
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

  void expectIteConflict(bool condition, bool downward)
  {
    ASTNode A = arr("A"), B = arr("B");
    // Keep the source condition distinct from its reified name. MapModel
    // intentionally knows only the latter, pinning the requirement that
    // propagation follows the SAT assignment rather than re-evaluating
    // the source term.
    ASTNode condTerm = mgr.CreateSymbol("condition_term", 0, 0);
    ASTNode condName = boolSym("condition_name", condition);
    ASTNode ite = arrayIte(condTerm, condName, A, B);
    const ASTNode& selected = condition ? A : B;
    ASTNode index = bv("index", 0);
    ASTNode iteValue = bv("ite_value", 1);
    ASTNode branchValue = bv("branch_value", 2);

    // All accesses are seeded before propagation. Whichever endpoint is
    // seeded first processes first and therefore determines whether the
    // first conflict is found by T-down or T-up.
    if (downward)
    {
      readAccess(ite, index, iteValue);
      readAccess(selected, index, branchValue);
    }
    else
    {
      readAccess(selected, index, branchValue);
      readAccess(ite, index, iteValue);
    }

    ExtCheckResult r = run();
    ASSERT_EQ(ExtCheckResult::CONFLICT, r.status);
    EXPECT_STREQ(downward ? "T_DOWN" : "T_UP", firstConflictRule(r));

    const ExtConflict& c = r.conflict;
    ASSERT_EQ(1u, c.rightGuards.size());
    EXPECT_TRUE(c.leftGuards.empty());
    EXPECT_EQ(condition ? ExtGuard::ITE_COND_POS
                        : ExtGuard::ITE_COND_NEG,
              c.rightGuards[0].kind);

    // The common index term is identical on both accesses, so
    // canonicalization drops its reflexive equality. The branch condition
    // is the complete premise, with the selected branch's polarity and
    // the correct term for each layer.
    ASSERT_EQ(1u, c.abstractPremise.size());
    EXPECT_TRUE(hasBoolGuard(c.abstractPremise, condName, condition));
    ASSERT_EQ(1u, c.theoryPremise.size());
    EXPECT_TRUE(hasBoolGuard(c.theoryPremise, condTerm, condition));
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

TEST_F(ExtFixtureTest, LongPropagationChainStoresLinksWithoutMaterializingPaths)
{
  const size_t length = 96;
  std::vector<ASTNode> arrays;
  arrays.reserve(length);
  for (size_t i = 0; i < length; ++i)
  {
    const std::string name = "chain_array_" + std::to_string(i);
    arrays.push_back(mgr.CreateSymbol(name.c_str(), 2, 2));
  }
  for (size_t i = 0; i + 1 < length; ++i)
  {
    const std::string name = "chain_eq_" + std::to_string(i);
    eqEdge(arrays[i], arrays[i + 1], name.c_str(), true);
  }

  readAccess(arrays[0], bv("chain_index", 1), bv("chain_value", 2));
  const ExtCheckResult r = run();
  ASSERT_EQ(ExtCheckResult::CONSISTENT, r.status);

  // One constant-size path record per reached pair. With no conflict, no
  // complete guard vector is ever reconstructed; the old copied-vector
  // representation retained 1+2+...+(length-1) guards here.
  EXPECT_EQ(length, r.proofPathEntries);
  EXPECT_EQ(0u, r.materializedGuardCount);
  expectStats(r, {{"insertions", static_cast<int>(length)},
                  {"propagations", static_cast<int>(length - 1)},
                  {"rule_R_EQ", static_cast<int>(length - 1)},
                  {"seeds", 1},
                  {"skipped_seen", static_cast<int>(length - 1)}});
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
  EXPECT_EQ(eqAB, c.rightGuards[0].absA);
  EXPECT_EQ(ExtGuard::EQ_PROXY, c.rightGuards[1].kind);
  EXPECT_EQ(eqBC, c.rightGuards[1].absA);
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

  size_t guardsInCertificates = 0;
  for (const ExtConflict& conflict : r.conflicts)
    guardsInCertificates +=
        conflict.leftGuards.size() + conflict.rightGuards.size();
  EXPECT_EQ(guardsInCertificates, r.materializedGuardCount);
}

TEST_F(ExtFixtureTest, IteTrueConditionPropagatesDownWithPositiveGuard)
{
  expectIteConflict(true, true);
}

TEST_F(ExtFixtureTest, IteFalseConditionPropagatesDownWithNegativeGuard)
{
  expectIteConflict(false, true);
}

TEST_F(ExtFixtureTest, IteTrueConditionPropagatesUpWithPositiveGuard)
{
  expectIteConflict(true, false);
}

TEST_F(ExtFixtureTest, IteFalseConditionPropagatesUpWithNegativeGuard)
{
  expectIteConflict(false, false);
}

TEST_F(ExtFixtureTest, IteDoesNotPropagateThroughUnselectedBranch)
{
  ASTNode A = arr("A"), B = arr("B");
  ASTNode condTerm = mgr.CreateSymbol("condition_term", 0, 0);
  ASTNode condName = boolSym("condition_name", true);
  ASTNode ite = arrayIte(condTerm, condName, A, B);
  ASTNode index = bv("index", 0);
  ASTNode iteValue = bv("ite_value", 1);
  ASTNode unselectedValue = bv("unselected_value", 2);

  readAccess(ite, index, iteValue);
  readAccess(B, index, unselectedValue);

  ExtCheckResult r = run();
  EXPECT_EQ(ExtCheckResult::CONSISTENT, r.status);
  EXPECT_TRUE(r.conflicts.empty());
  expectStats(r, {{"insertions", 3},
                  {"propagations", 1},
                  {"rule_T_DOWN", 1},
                  {"seeds", 2},
                  {"skipped_seen", 1}});
}

// Direct tests for the solve-time preparation layer: recovering the
// canonical equality operands from the witness anchors, collecting the
// complete owned array graph, retaining array-valued if-then-else terms,
// scalar naming, the exact hand-off to ArrayTransformer, and loud failures
// when a solve-boundary invariant is broken.  These avoid SAT, so a
// preparation/transform integration regression fails here instead of as a
// distant error inside a full solve.
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

  const ASTNode rawEquality = hf->CreateNode(EQ, w, b);
  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(rawEquality);
  ASSERT_EQ(SYMBOL, proxy.GetKind());
  ASSERT_EQ(1u, ext->getRecords().size());

  ASTNode root = ext->conjoinRecordConstraints(proxy);
  ext->prepare(root);

  // Nothing rewrote the formula between construction and preparation,
  // so anchor recovery must reproduce the construction operands
  // exactly.
  const ExtensionalityContext::Record& r = ext->getRecords()[0];
  EXPECT_EQ(r.constructionLeft, r.canonicalLeft);
  EXPECT_EQ(r.constructionRight, r.canonicalRight);

  // The complete graph contains both operands and the write's base.
  EXPECT_TRUE(ext->arrayGraphFrozen());
  EXPECT_TRUE(ext->ownsArray(w));
  EXPECT_TRUE(ext->ownsArray(b));
  EXPECT_TRUE(ext->ownsArray(a));

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

TEST_F(ExtPrepareTest, OwnsArraysDisconnectedFromTheActivatingEquality)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), x = arr("x");
  ASTNode i = bv("i");

  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(hf->CreateNode(EQ, a, b));
  ASTNode unrelatedRead = hf->CreateTerm(READ, 2, x, i);
  ASTNode root = ext->conjoinRecordConstraints(hf->CreateNode(
      AND, proxy, hf->CreateNode(EQ, unrelatedRead, mgr.CreateZeroConst(2))));

  // Protection is computed before simplification, and final ownership is
  // computed independently from equality reachability.
  EXPECT_TRUE(ext->wasArrayAnticipated(x));
  ext->prepare(root);
  EXPECT_TRUE(ext->ownsArray(a));
  EXPECT_TRUE(ext->ownsArray(b));
  EXPECT_TRUE(ext->ownsArray(x));
}

TEST_F(ExtPrepareTest, ArrayIteIsKeptAndReasonedAboutDirectly)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), d = arr("d");
  ASTNode c = mgr.CreateSymbol("c", 0, 0);

  // Building an array-valued if-then-else builds one, and moves no
  // solver state.
  ASTNode ite = hf->CreateArrayTerm(ITE, 2, 2, {c, a, b});
  EXPECT_EQ(ITE, ite.GetKind());
  EXPECT_EQ(0u, ext->getRecords().size());

  // An equality over it is one ordinary record -- and stays the only
  // one. Section 4.1's rewriting would have charged a second array
  // variable and two more equality records here, each with a witness
  // index and two virtual reads; direct integration charges one
  // reified Boolean.
  const ASTNode rawEquality = hf->CreateNode(EQ, ite, d);
  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(rawEquality);
  ASSERT_EQ(1u, ext->getRecords().size());

  ext->prepare(ext->conjoinRecordConstraints(proxy));
  EXPECT_EQ(1u, ext->getRecords().size());
  const size_t protectedAfterFirstSolve = ext->getFrozenSymbols().size();

  // The if-then-else is in the graph as itself, with both branches
  // reachable through it -- that is what rules T-down and T-up walk.
  EXPECT_TRUE(ext->ownsArray(ite));
  EXPECT_TRUE(ext->ownsArray(a));
  EXPECT_TRUE(ext->ownsArray(b));

  // The operand recovered for the user's equality is the if-then-else,
  // not a stand-in for it.
  const ExtensionalityContext::Record& r = ext->getRecords()[0];
  const ASTNode operand =
      (r.canonicalLeft == d) ? r.canonicalRight : r.canonicalLeft;
  EXPECT_EQ(ite, operand);

  // A second solve moves nothing.
  ext->beginSolve();
  proxy = ext->lowerArrayEqualities(rawEquality);
  ext->prepare(ext->conjoinRecordConstraints(proxy));
  EXPECT_EQ(1u, ext->getRecords().size());
  EXPECT_EQ(protectedAfterFirstSolve, ext->getFrozenSymbols().size());
}

TEST_F(ExtPrepareTest, IteConditionIsReifiedAsAProtectedName)
{
  // The checker decides which branch is live from sigma(condition). It
  // must read the value the SAT solver assigned, not one re-derived
  // from the counterexample: a name that disagrees with its term makes
  // the wrong branch live and can certify a model that does not satisfy
  // the if-then-else axiom. That is the failure class that produced a
  // sat answer on an unsatisfiable query once already on this branch.
  //
  // So the condition gets a reified Boolean of its own, protected from
  // substitution like every other name the procedure depends on, and
  // bound to the condition by the naming constraints preparation
  // conjoins. It is also what a lemma premise names, since encoding
  // needs one fully encoded literal.
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), d = arr("d");
  ASTNode x = bv("x"), y = bv("y");
  // A compound condition, so the name cannot merely be the term.
  ASTNode cond = hf->CreateNode(EQ, x, y);
  ASTNode ite = hf->CreateArrayTerm(ITE, 2, 2, {cond, a, b});

  ext->beginSolve();
  ASTNode proxy =
      ext->lowerArrayEqualities(hf->CreateNode(EQ, ite, d));
  ext->prepare(ext->conjoinRecordConstraints(proxy));

  const std::map<ASTNode, ASTNode>& n2t = ext->getNameToTerm();
  bool named = false;
  for (std::map<ASTNode, ASTNode>::const_iterator it = n2t.begin();
       it != n2t.end(); ++it)
  {
    EXPECT_TRUE(ext->isProtected(it->first));
    if (it->second == cond)
    {
      named = true;
      EXPECT_EQ(SYMBOL, it->first.GetKind());
      EXPECT_EQ(0u, it->first.GetValueWidth()); // Boolean
    }
  }
  EXPECT_TRUE(named);
}

TEST_F(ExtPrepareTest, MissingAnchorFailsLoudly)
{
  ASTNode a = arr("a"), b = arr("b");
  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(
      mgr.hashingNodeFactory->CreateNode(EQ, ASTVec{a, b}));
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
  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(hf->CreateNode(EQ, a, b));
  (void)proxy;
  ASSERT_EQ(1u, ext->getRecords().size());
  const ExtensionalityContext::Record r = ext->getRecords()[0];

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
  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(hf->CreateNode(EQ, a, b));
  (void)proxy;
  ASSERT_EQ(1u, ext->getRecords().size());
  const ExtensionalityContext::Record r = ext->getRecords()[0];

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

// The pre-preprocessing boundary snapshots every array symbol in the
// complete root. If the prepared graph contains a symbol absent from that
// snapshot, its reads may already have been substituted away. This test
// deliberately bypasses conjoinRecordConstraints and supplies such a graph.
TEST_F(ExtPrepareTest, UnanticipatedArraySymbolFailsLoudly)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), z = arr("z");
  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(hf->CreateNode(EQ, a, b));
  (void)proxy;
  ASSERT_EQ(1u, ext->getRecords().size());
  const ExtensionalityContext::Record r = ext->getRecords()[0];

  // Stands in for a pass that introduced z after the ownership boundary.
  ASTVec conjuncts;
  conjuncts.push_back(
      hf->CreateNode(EQ, r.nameL, hf->CreateTerm(READ, 2, z, r.lambda)));
  conjuncts.push_back(r.anchorR);
  conjuncts.push_back(r.witnessClause);
  EXPECT_DEATH(ext->prepare(hf->CreateNode(AND, conjuncts)),
               "entered the prepared graph without appearing");
}

// An array reachable ONLY as the far branch of an array if-then-else
// above an equality operand. Reduced from a murxla find:
//
//   (assert (bvuge x (select (ite (distinct b z') b a) x)))
//
// where the only equality is over b and z'. No equality operand mentions a,
// and it cannot exist when that equality is built because the equality is
// the if-then-else condition. The complete-root ownership snapshot must
// nevertheless anticipate a before preprocessing begins.
TEST_F(ExtPrepareTest, ArrayReachableOnlyThroughAnIteBranchIsAnticipated)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), z = arr("z");
  ASTNode i = bv("i");

  // The equality is over b and z. Its own proxy is the if-then-else
  // condition, so the if-then-else cannot exist before the equality.
  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(hf->CreateNode(EQ, b, z));
  ASSERT_EQ(1u, ext->getRecords().size());
  EXPECT_FALSE(ext->wasArrayAnticipated(a));

  ASTNode ite = hf->CreateArrayTerm(ITE, 2, 2, {hf->CreateNode(NOT, proxy), b, a});
  ASTNode read = hf->CreateTerm(READ, 2, ite, i);

  ASTNode root = ext->conjoinRecordConstraints(
      hf->CreateNode(EQ, read, mgr.CreateZeroConst(2)));

  // Anticipated by the time any pass could delete a read over it.
  EXPECT_TRUE(ext->wasArrayAnticipated(a));

  // And it really is owned after preparation.
  ext->prepare(root);
  EXPECT_TRUE(ext->ownsArray(a));
  EXPECT_TRUE(ext->ownsArray(b));
  EXPECT_TRUE(ext->ownsArray(ite));
}

TEST_F(ExtPrepareTest, ExactReadInventorySurvivesNamingAndIndexAliases)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), x = arr("x");
  ASTNode i = bv("i"), j = bv("j"), k = bv("k");
  ASTNode nested = hf->CreateTerm(READ, 2, x, i);

  // The same nested read is both a write index and value.  The active
  // transform deliberately does not descend through the array operand of a
  // witness read; preparation's scalar naming equations are what expose this
  // read to the transform, and the final-root inventory must include it.
  ASTNode w = hf->CreateArrayTerm(WRITE, 2, 2, {a, nested, nested});

  // These are distinct source READ nodes but their indices transform to the
  // same j.  Both source nodes must be accounted for while the transformer
  // table contains exactly one (x,j) row.
  ASTNode selectedIndex =
      hf->CreateTerm(ITE, 2, {mgr.ASTTrue, j, k});
  ASTNode selectedRead = hf->CreateTerm(READ, 2, x, selectedIndex);
  ASTNode directRead = hf->CreateTerm(READ, 2, x, j);

  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(hf->CreateNode(EQ, w, b));
  ASTVec conjuncts;
  conjuncts.push_back(proxy);
  conjuncts.push_back(
      hf->CreateNode(EQ, selectedRead, mgr.CreateZeroConst(2)));
  conjuncts.push_back(
      hf->CreateNode(EQ, directRead, mgr.CreateOneConst(2)));
  ASTNode prepared = ext->prepare(
      ext->conjoinRecordConstraints(hf->CreateNode(AND, conjuncts)));

  SubstitutionMap substitutions(&mgr);
  Simplifier simplifier(&mgr, &substitutions);
  ArrayTransformer transformer(&mgr, &simplifier);
  transformer.TransformFormula_TopLevel(prepared);
  ext->bindAfterTransform(&transformer);

  EXPECT_TRUE(ext->checkerReady());
  ArrayTransformer::ArrType::const_iterator xRows =
      transformer.arrayToIndexToRead.find(x);
  ASSERT_NE(transformer.arrayToIndexToRead.end(), xRows);
  EXPECT_EQ(2u, xRows->second.size()); // (x,i) and the shared (x,j)
}

TEST_F(ExtPrepareTest, ConstantTermIteAccountsForDeadReadSubtree)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), x = arr("x");
  ASTNode i = bv("i");
  ASTNode deadRead = hf->CreateTerm(READ, 2, x, i);
  ASTNode selected = hf->CreateTerm(
      ITE, 2, {mgr.ASTTrue, mgr.CreateZeroConst(2), deadRead});

  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(hf->CreateNode(EQ, a, b));
  ASTNode root = ext->conjoinRecordConstraints(hf->CreateNode(
      AND, proxy, hf->CreateNode(EQ, selected, mgr.CreateZeroConst(2))));
  ASTNode prepared = ext->prepare(root);

  SubstitutionMap substitutions(&mgr);
  Simplifier simplifier(&mgr, &substitutions);
  ArrayTransformer transformer(&mgr, &simplifier);
  transformer.TransformFormula_TopLevel(prepared);
  ext->bindAfterTransform(&transformer);

  EXPECT_TRUE(ext->checkerReady());
  EXPECT_EQ(transformer.arrayToIndexToRead.end(),
            transformer.arrayToIndexToRead.find(x));
}

TEST_F(ExtPrepareTest, MissingPreparedReadDispositionFailsLoudly)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b");

  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(hf->CreateNode(EQ, a, b));
  ASTNode prepared = ext->prepare(ext->conjoinRecordConstraints(proxy));
  ext->beginReadTransform(prepared);

  // Even the two mandatory witness reads have not been reported.  Binding a
  // partial inventory must be impossible, rather than delegated to whichever
  // refinement subsystem happens to see the missing read later.
  EXPECT_DEATH(ext->finishReadTransform(),
               "neither abstracted nor eliminated");
}

TEST_F(ExtPrepareTest, OpaqueEqualityAtFinalBoundaryFailsLoudly)
{
  NodeFactory* hf = mgr.hashingNodeFactory;
  ASTNode a = arr("a"), b = arr("b"), x = arr("x"), y = arr("y");

  ext->beginSolve();
  ASTNode proxy = ext->lowerArrayEqualities(hf->CreateNode(EQ, a, b));

  // Simulate a future pass reintroducing an opaque equality after the one
  // authorized lowering traversal.  Preparation is the final word-level
  // boundary and must reject it before ordinary simplification/transform.
  ASTNode rogue = hf->CreateNode(ARRAY_EQ, x, y);
  ASTNode root =
      ext->conjoinRecordConstraints(hf->CreateNode(AND, proxy, rogue));
  EXPECT_DEATH(ext->prepare(root), "opaque equality reached the final");
}

// The decision table combining STP's own model evaluation with the
// array consistency check: an array conflict always takes priority
// (only its lemma can rule the candidate out), and a candidate is
// satisfiable only when both checks pass. All sixteen cells.
TEST(ExtCertification, TruthTable)
{
  typedef ExtensionalityContext EC;
  // checker inactive: EXTCHK skipped; ordinary result decides. (A
  // consistent verdict without an active checker is tolerated identically;
  // conflict or witness trouble from a checker that had nothing to
  // check is an internal error.)
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
  // checker active: EXTCHK conflict has priority over both ordinary
  // results; SAT only for ordinary-true + consistent; a skipped check
  // despite an active checker is an internal error whatever the
  // ordinary result was. A consistent checker paired with ordinary
  // false is likewise an internal error: the checker owns every array
  // read, so there is no host-refinement partition left to repair it.
  EXPECT_EQ(EC::RETURN_SAT,
            EC::decideCertification(true, true, EC::EXT_CONSISTENT));
  EXPECT_EQ(EC::ADD_EXT_LEMMA,
            EC::decideCertification(true, true, EC::EXT_CONFLICT));
  EXPECT_EQ(EC::INTERNAL_ERROR,
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
}

} // namespace

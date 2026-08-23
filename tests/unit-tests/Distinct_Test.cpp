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

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Parser/parser.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/DistinctOrdering.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <sstream>

using namespace stp;

namespace
{

TEST(DistinctAst, IsNativeVariadicTypedAndSourceOrdered)
{
  STPMgr mgr;
  const ASTNode x = mgr.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode y = mgr.CreateSourceSymbol("y", SourceSort::bitVector(8));
  const ASTNode z = mgr.CreateSourceSymbol("z", SourceSort::bitVector(8));

  const ASTNode distinct = mgr.CreateNode(DISTINCT, ASTVec{z, x, y});
  ASSERT_EQ(DISTINCT, distinct.GetKind());
  ASSERT_EQ(3u, distinct.Degree());
  EXPECT_EQ(z, distinct[0]);
  EXPECT_EQ(x, distinct[1]);
  EXPECT_EQ(y, distinct[2]);
  EXPECT_TRUE(distinct.isPred());
  EXPECT_TRUE(BVTypeCheck(distinct));
  EXPECT_TRUE(mgr.has_distinct);

  std::ostringstream out;
  printer::SMTLIB2_Print1(out, distinct, 0, false);
  EXPECT_EQ("(distinct |z| |x| |y|)", out.str());
}

TEST(DistinctAst, FactoryRejectsMalformedAndMixedSortPredicates)
{
  STPMgr mgr;
  const ASTNode x = mgr.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode y = mgr.CreateSourceSymbol("y", SourceSort::bitVector(16));

  EXPECT_DEATH(mgr.CreateNode(DISTINCT, ASTVec{x}), "at least two operands");
  EXPECT_DEATH(mgr.CreateNode(DISTINCT, ASTVec{x, y}),
               "identical source sorts");

  const SourceSort arrays =
      SourceSort::array(SourceSort::bitVector(2), SourceSort::bitVector(3));
  const ASTNode a = mgr.CreateSourceSymbol("a", arrays);
  const ASTNode b = mgr.CreateSourceSymbol("b", arrays);
  EXPECT_DEATH(mgr.CreateNode(DISTINCT, ASTVec{a, b}),
               "cannot decide equality between whole array terms");
}

TEST(DistinctAst, LoweringUsesEqualityForEachSourceSort)
{
  STPMgr mgr;

  const ASTNode x = mgr.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode y = mgr.CreateSourceSymbol("y", SourceSort::bitVector(8));
  const ASTNode z = mgr.CreateSourceSymbol("z", SourceSort::bitVector(8));
  const ASTNode lowered =
      lowerDistinct(&mgr, mgr.CreateNode(DISTINCT, ASTVec{x, y, z}));
  ASSERT_EQ(AND, lowered.GetKind());
  ASSERT_EQ(3u, lowered.Degree());
  for (const ASTNode& disequality : lowered)
  {
    ASSERT_EQ(NOT, disequality.GetKind());
    ASSERT_EQ(EQ, disequality[0].GetKind());
  }
  EXPECT_FALSE(containsKind(lowered, DISTINCT));

  const ASTNode p = mgr.CreateSourceSymbol("p", SourceSort::boolean());
  const ASTNode q = mgr.CreateSourceSymbol("q", SourceSort::boolean());
  const ASTNode boolLowered =
      lowerDistinct(&mgr, mgr.CreateNode(DISTINCT, ASTVec{p, q}));
  ASSERT_EQ(NOT, boolLowered.GetKind());
  EXPECT_EQ(IFF, boolLowered[0].GetKind());

  const SourceSort fp = SourceSort::floatingPoint(8, 24);
  const ASTNode f = mgr.CreateSourceSymbol("f", fp);
  const ASTNode g = mgr.CreateSourceSymbol("g", fp);
  const ASTNode fpLowered =
      lowerDistinct(&mgr, mgr.CreateNode(DISTINCT, ASTVec{f, g}));
  ASSERT_EQ(NOT, fpLowered.GetKind());
  EXPECT_EQ(FP_SMT_EQ, fpLowered[0].GetKind());

  mgr.UserFlags.enable_array_equality = true;
  const SourceSort arrays =
      SourceSort::array(SourceSort::bitVector(2), SourceSort::bitVector(3));
  const ASTNode a = mgr.CreateSourceSymbol("a", arrays);
  const ASTNode b = mgr.CreateSourceSymbol("b", arrays);
  const ASTNode arrayLowered =
      lowerDistinct(&mgr, mgr.CreateNode(DISTINCT, ASTVec{a, b}));
  ASSERT_EQ(NOT, arrayLowered.GetKind());
  EXPECT_EQ(ARRAY_EQ, arrayLowered[0].GetKind());
}

TEST(DistinctAst, OrderingConsumesNativePredicateDirectly)
{
  STPMgr mgr;
  const ASTNode x = mgr.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode y = mgr.CreateSourceSymbol("y", SourceSort::bitVector(8));
  const ASTNode z = mgr.CreateSourceSymbol("z", SourceSort::bitVector(8));
  const ASTNode distinct = mgr.CreateNode(DISTINCT, ASTVec{x, y, z});

  size_t ordered = 0;
  const ASTNode result = applyDistinctOrdering(&mgr, distinct, &ordered);
  EXPECT_EQ(1u, ordered);
  EXPECT_FALSE(containsKind(result, DISTINCT));
  EXPECT_TRUE(containsKind(result, BVLT));

  const ASTNode escaped =
      mgr.CreateNode(AND, distinct, mgr.CreateNode(BVLT, y, x));
  EXPECT_EQ(escaped, applyDistinctOrdering(&mgr, escaped, &ordered));
  EXPECT_EQ(0u, ordered);
}

TEST(DistinctAst, Smt2ParserPreservesNativePredicate)
{
  STPMgr mgr;
  SimplifyingNodeFactory simplifying(*mgr.hashingNodeFactory, mgr);
  Cpp_interface interface(mgr, &simplifying);
  mgr.defaultNodeFactory = &simplifying;
  interface.startup();
  GlobalParserBM = &mgr;
  GlobalParserInterface = &interface;

  SMT2ScanString(R"(
    (set-logic QF_BV)
    (declare-const z (_ BitVec 8))
    (declare-const x (_ BitVec 8))
    (declare-const y (_ BitVec 8))
    (assert (distinct z x y))
  )");
  ASSERT_EQ(0, SMT2Parse());
  smt2lex_destroy();

  const ASTVec assertions = mgr.GetAsserts();
  ASSERT_EQ(1u, assertions.size());
  ASSERT_EQ(DISTINCT, assertions[0].GetKind());
  std::ostringstream out;
  printer::SMTLIB2_Print1(out, assertions[0], 0, false);
  EXPECT_EQ("(distinct |z| |x| |y|)", out.str());
}

IncrementalSolver::EncodingEpochStats
incrementalDistinctEncoding(const bool ordering)
{
  STPMgr mgr;
  mgr.UserFlags.distinct_ordering = ordering;
  // Keep the comparison about the solve-boundary representation itself: no
  // optional preprocessing should erase or repartition either form.
  mgr.UserFlags.optimize_flag = false;
  mgr.UserFlags.incremental_core_only = true;

  SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  ArrayTransformer at(&mgr, &simp);
  AbsRefine_CounterExample ce(&mgr, &simp, &at);
  IncrementalSolver incremental(&mgr, &ce, &simp, &at);

  ASTVec operands;
  for (unsigned i = 0; i < 12; ++i)
  {
    std::ostringstream name;
    name << "incremental_distinct_" << i;
    const std::string symbolName = name.str();
    operands.push_back(
        mgr.CreateSourceSymbol(symbolName.c_str(), SourceSort::bitVector(8)));
  }
  const ASTNode distinct = mgr.CreateNode(DISTINCT, operands);
  EXPECT_EQ(SOLVER_SATISFIABLE,
            incremental.checkSat(ASTVec(1, distinct)));
  return incremental.encodingEpochStatsForTesting();
}

TEST(DistinctAst, IncrementalOrderingAvoidsPairwiseEncoding)
{
  const IncrementalSolver::EncodingEpochStats ordered =
      incrementalDistinctEncoding(true);
  const IncrementalSolver::EncodingEpochStats pairwise =
      incrementalDistinctEncoding(false);

  // The ordered solve encodes one assumption-scoped completed root. With the
  // optimization disabled, semantic lowering exposes C(12,2) base conjuncts.
  EXPECT_EQ(1u, ordered.rootEncodings);
  EXPECT_EQ(66u, pairwise.rootEncodings);
  EXPECT_LT(ordered.aigAndNodes, pairwise.aigAndNodes);
}

} // namespace

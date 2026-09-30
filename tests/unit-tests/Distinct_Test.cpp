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

TEST(DistinctAst, DefaultSymbolUseBlocksOnlyItsOwnOrderingGroup)
{
  STPMgr mgr;
  const SourceSort bv8 = SourceSort::bitVector(8);
  const SourceSort arrays = SourceSort::array(bv8, bv8);
  const ASTNode x = mgr.CreateSourceSymbol("default_x", bv8);
  const ASTNode y = mgr.CreateSourceSymbol("default_y", bv8);
  const ASTNode z = mgr.CreateSourceSymbol("default_z", bv8);
  const ASTNode blocked = mgr.CreateNode(DISTINCT, ASTVec{x, y, z});
  const ASTNode array = mgr.CreateConstArray(arrays, x);
  const ASTNode other = mgr.CreateSourceSymbol("default_array", arrays);
  const ASTNode equality = mgr.CreateNode(ARRAY_EQ, array, other);
  const ASTNode root = mgr.CreateNode(AND, blocked, equality);

  size_t ordered = 0;
  EXPECT_EQ(root, applyDistinctOrdering(&mgr, root, &ordered));
  EXPECT_EQ(0u, ordered);

  const ASTNode a = mgr.CreateSourceSymbol("independent_a", bv8);
  const ASTNode b = mgr.CreateSourceSymbol("independent_b", bv8);
  const ASTNode c = mgr.CreateSourceSymbol("independent_c", bv8);
  const ASTNode independent = mgr.CreateNode(DISTINCT, ASTVec{a, b, c});
  const ASTNode combined = mgr.CreateNode(AND, root, independent);
  const ASTNode result = applyDistinctOrdering(&mgr, combined, &ordered);
  EXPECT_EQ(1u, ordered);
  EXPECT_TRUE(containsKind(result, DISTINCT, true));
  EXPECT_TRUE(containsKind(result, BVLT, true));
  EXPECT_EQ(x, mgr.constArrayDefault(array));
}

TEST(DistinctAst, SharedAssertionAndBooleanDefaultHasBothPolarities)
{
  STPMgr mgr;
  const SourceSort bv8 = SourceSort::bitVector(8);
  const SourceSort arrays = SourceSort::array(bv8, SourceSort::boolean());
  const ASTNode x = mgr.CreateSourceSymbol("shared_x", bv8);
  const ASTNode y = mgr.CreateSourceSymbol("shared_y", bv8);
  const ASTNode z = mgr.CreateSourceSymbol("shared_z", bv8);
  const ASTNode distinct = mgr.CreateNode(DISTINCT, ASTVec{x, y, z});
  const ASTNode array = mgr.CreateConstArray(arrays, distinct);
  const ASTNode other = mgr.CreateSourceSymbol("shared_array", arrays);
  const ASTNode root = mgr.CreateNode(
      AND, distinct, mgr.CreateNode(ARRAY_EQ, array, other));

  // The assertion alone is eligible. Reaching the identical node as array
  // data must add both polarities, even if the assertion was visited first.
  size_t ordered = 0;
  applyDistinctOrdering(&mgr, distinct, &ordered);
  ASSERT_EQ(1u, ordered);
  EXPECT_EQ(root, applyDistinctOrdering(&mgr, root, &ordered));
  EXPECT_EQ(0u, ordered);
  EXPECT_TRUE(containsKind(mgr.constArrayDefault(array), DISTINCT, true));
}

TEST(DistinctAst, LoweringRebuildsNestedDefaultsWithoutMutatingTheirHandles)
{
  STPMgr mgr;
  const SourceSort bv8 = SourceSort::bitVector(8);
  const SourceSort arrays = SourceSort::array(bv8, bv8);
  const ASTNode x = mgr.CreateSourceSymbol("nested_x", bv8);
  const ASTNode y = mgr.CreateSourceSymbol("nested_y", bv8);
  const ASTNode z = mgr.CreateSourceSymbol("nested_z", bv8);
  const ASTNode distinct = mgr.CreateNode(DISTINCT, ASTVec{x, y, z});
  const ASTNode zero = mgr.CreateZeroConst(8);
  const ASTNode value = mgr.CreateTerm(
      ITE, 8, distinct, mgr.CreateOneConst(8), zero);
  const ASTNode inner = mgr.CreateConstArray(arrays, value);
  const ASTNode i = mgr.CreateSourceSymbol("nested_i", bv8);
  const ASTNode j = mgr.CreateSourceSymbol("nested_j", bv8);
  // A direct read would fold to the default before lowering sees the array.
  const ASTNode store =
      mgr.CreateArrayTerm(WRITE, 8, 8, ASTVec{inner, i, zero});
  const ASTNode read = mgr.CreateTerm(READ, 8, store, j);
  const ASTNode outer = mgr.CreateConstArray(arrays, read);
  ASSERT_FALSE(containsKind(outer, DISTINCT));
  ASSERT_TRUE(containsKind(outer, DISTINCT, true));

  const ASTNode lowered = lowerDistinct(&mgr, outer);
  ASSERT_TRUE(mgr.isConstArray(lowered));
  EXPECT_NE(outer, lowered);
  EXPECT_EQ(arrays, lowered.GetSourceSort());
  EXPECT_FALSE(containsKind(lowered, DISTINCT, true));
  EXPECT_TRUE(containsKind(lowered, EQ, true));
  EXPECT_EQ(value, mgr.constArrayDefault(inner));
  EXPECT_EQ(read, mgr.constArrayDefault(outer));
  EXPECT_TRUE(containsKind(outer, DISTINCT, true));
  EXPECT_EQ(outer, mgr.CreateConstArray(arrays, read));
  EXPECT_EQ(lowered, lowerDistinct(&mgr, lowered));
}

TEST(DistinctAst, LoweringPreservesPackedBooleanDefaults)
{
  STPMgr mgr;
  const SourceSort arrays = SourceSort::array(
      SourceSort::bitVector(8), SourceSort::boolean());
  const ASTNode p = mgr.CreateSourceSymbol("packed_p", SourceSort::boolean());
  const ASTNode q = mgr.CreateSourceSymbol("packed_q", SourceSort::boolean());
  const ASTNode distinct = mgr.CreateNode(DISTINCT, ASTVec{p, q});
  const ASTNode array = mgr.CreateConstArray(arrays, distinct);
  const ASTNode originalDefault = mgr.constArrayDefault(array);
  ASSERT_EQ(ITE, originalDefault.GetKind());
  ASSERT_EQ(distinct, originalDefault[0]);

  const ASTNode lowered = lowerDistinct(&mgr, array);
  ASSERT_TRUE(mgr.isConstArray(lowered));
  EXPECT_EQ(arrays, lowered.GetSourceSort());
  const ASTNode packed = mgr.constArrayDefault(lowered);
  ASSERT_EQ(ITE, packed.GetKind());
  EXPECT_EQ(1u, packed.GetValueWidth());
  EXPECT_EQ(lowerDistinct(&mgr, distinct), packed[0]);
  EXPECT_EQ(mgr.CreateOneConst(1), packed[1]);
  EXPECT_EQ(mgr.CreateZeroConst(1), packed[2]);
  EXPECT_FALSE(containsKind(lowered, DISTINCT, true));
  EXPECT_EQ(originalDefault, mgr.constArrayDefault(array));
  EXPECT_EQ(array, mgr.CreateConstArray(arrays, distinct));
  EXPECT_EQ(lowered, lowerDistinct(&mgr, lowered));
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

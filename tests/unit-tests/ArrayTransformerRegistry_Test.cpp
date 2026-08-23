/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include <gtest/gtest.h>
#include <utility>

using namespace stp;

namespace
{

ASTNode readEquals(STPMgr& mgr, const ASTNode& array, const ASTNode& index,
                   unsigned value)
{
  NodeFactory* nf = mgr.defaultNodeFactory;
  const ASTNode read = nf->CreateTerm(READ, array.GetValueWidth(), array,
                                      index);
  return nf->CreateNode(
      EQ, read, mgr.CreateBVConst(array.GetValueWidth(), value));
}

TEST(ArrayTransformerRegistry, transform_restores_the_batch_registry)
{
  STPMgr mgr;
  SubstitutionMap substitutions(&mgr);
  Simplifier simplifier(&mgr, &substitutions);
  ArrayTransformer transformer(&mgr, &simplifier);
  ArrayTransformer::Registry persistent;

  const ASTNode batchArray = mgr.CreateSymbol("batch-array", 4, 8);
  const ASTNode batchIndex = mgr.CreateSymbol("batch-index", 0, 4);
  const ASTNode batchValue = mgr.CreateSymbol("batch-value", 0, 8);
  transformer.arrayToIndexToRead[batchArray].insert(std::make_pair(
      batchIndex,
      ArrayTransformer::ArrayRead(batchValue, batchValue)));

  const ASTNode array = mgr.CreateSymbol("persistent-array", 4, 8);
  const ASTNode index = mgr.CreateSymbol("persistent-index", 0, 4);
  const ASTNode formula = readEquals(mgr, array, index, 7);

  ArrayTransformer::TransformResult first =
      transformer.TransformFormulaWithRegistry(formula, persistent);
  EXPECT_FALSE(containsArrayOps(first.formula, &mgr));
  ASSERT_EQ(1u, first.touchedReads.size());
  EXPECT_EQ(ArrayTransformer::ReadKey(array, index), first.touchedReads[0]);
  ASSERT_EQ(1u, persistent.reads.count(array));
  EXPECT_EQ(1u, persistent.reads.at(array).count(index));

  // The transaction returns the transformer's pre-existing batch table and
  // keeps the persistent rows out of it.
  ASSERT_EQ(1u, transformer.arrayToIndexToRead.count(batchArray));
  EXPECT_EQ(1u,
            transformer.arrayToIndexToRead.at(batchArray).count(batchIndex));
  EXPECT_EQ(0u, transformer.arrayToIndexToRead.count(array));

  // Registry hits are reported as touched too, which is what lets the
  // incremental driver reconstruct the active rows on a cache hit later.
  ArrayTransformer::TransformResult second =
      transformer.TransformFormulaWithRegistry(formula, persistent);
  ASSERT_EQ(1u, second.touchedReads.size());
  EXPECT_EQ(ArrayTransformer::ReadKey(array, index), second.touchedReads[0]);
  EXPECT_EQ(1u, persistent.reads.at(array).size());
  EXPECT_EQ(0u, transformer.arrayToIndexToRead.count(array));
}

TEST(ArrayTransformerRegistry, eager_ackermann_pairs_persist_with_reads)
{
  STPMgr mgr;
  mgr.UserFlags.ackermannisation = true;
  SubstitutionMap substitutions(&mgr);
  Simplifier simplifier(&mgr, &substitutions);
  ArrayTransformer transformer(&mgr, &simplifier);
  ArrayTransformer::Registry persistent;

  const ASTNode array = mgr.CreateSymbol("eager-array", 4, 8);
  const ASTNode i = mgr.CreateSymbol("eager-i", 0, 4);
  const ASTNode j = mgr.CreateSymbol("eager-j", 0, 4);

  ArrayTransformer::TransformResult first =
      transformer.TransformFormulaWithRegistry(readEquals(mgr, array, i, 1),
                                               persistent);
  ASSERT_EQ(1u, first.touchedReads.size());
  ASSERT_EQ(1u, persistent.ackPairs.count(array));
  EXPECT_EQ(1u, persistent.ackPairs.at(array).all.size());

  ArrayTransformer::TransformResult second =
      transformer.TransformFormulaWithRegistry(readEquals(mgr, array, j, 2),
                                               persistent);
  ASSERT_EQ(1u, second.touchedReads.size());
  EXPECT_EQ(ArrayTransformer::ReadKey(array, j), second.touchedReads[0]);
  EXPECT_EQ(2u, persistent.reads.at(array).size());
  EXPECT_EQ(2u, persistent.ackPairs.at(array).all.size());

  persistent.releaseStorage();
  EXPECT_TRUE(persistent.reads.empty());
  EXPECT_TRUE(persistent.ackPairs.empty());
}

} // namespace

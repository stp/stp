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

/*
 * The lazy write-chain read abstraction in ArrayTransformer: reads over a
 * deep may-alias write chain become chain rows once enough reads share the
 * base array, and stay eagerly expanded below the depth and popularity
 * thresholds or under the eager-Ackermann regime.
 */

#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>

using namespace stp;

namespace
{

struct Harness
{
  STPMgr mgr;
  SubstitutionMap sm;
  Simplifier simp;
  ArrayTransformer at;

  Harness() : sm(&mgr), simp(&mgr, &sm), at(&mgr, &simp)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;
  }

  // AND over `reads` reads of a `depth`-store chain of symbolic indexes
  // and values, each pinned against a distinct constant.
  ASTNode chainFormula(unsigned depth, unsigned reads)
  {
    NodeFactory* nf = mgr.defaultNodeFactory;
    ASTNode chain = mgr.CreateSymbol("arr", 8, 8);
    for (unsigned k = 0; k < depth; k++)
    {
      const ASTNode i =
          mgr.CreateSymbol(("wi" + std::to_string(k)).c_str(), 0, 8);
      const ASTNode v =
          mgr.CreateSymbol(("wv" + std::to_string(k)).c_str(), 0, 8);
      chain = nf->CreateArrayTerm(WRITE, 8, 8, chain, i, v);
    }
    ASTVec conjuncts;
    for (unsigned r = 0; r < reads; r++)
    {
      const ASTNode j =
          mgr.CreateSymbol(("j" + std::to_string(r)).c_str(), 0, 8);
      const ASTNode read = nf->CreateTerm(READ, 8, chain, j);
      conjuncts.push_back(
          nf->CreateNode(EQ, read, mgr.CreateBVConst(8, r + 1)));
    }
    return (conjuncts.size() == 1) ? conjuncts[0]
                                   : nf->CreateNode(AND, conjuncts);
  }

  size_t rowsAfterTransform(unsigned depth, unsigned reads)
  {
    const ASTNode transformed =
        at.TransformFormula_TopLevel(chainFormula(depth, reads));
    (void)transformed;
    size_t rows = 0;
    for (ArrayTransformer::ChainReadsMap::const_iterator it =
             at.chainReads.begin();
         it != at.chainReads.end(); it++)
      rows += it->second.size();
    return rows;
  }
};

TEST(LazyWriteChainReads, deep_shared_chain_is_abstracted)
{
  Harness s;
  // 8 may-alias levels, 8 reads: past both thresholds. The first arrivals
  // stay eager, so fewer rows than reads -- but some must exist, each with
  // the residual chain and the base fall-through recorded.
  const size_t rows = s.rowsAfterTransform(8, 8);
  EXPECT_GT(rows, 0u);
  EXPECT_LT(rows, 8u);
  for (ArrayTransformer::ChainReadsMap::const_iterator it =
           s.at.chainReads.begin();
       it != s.at.chainReads.end(); it++)
    for (ArrayTransformer::ChainIndexMap::const_iterator rit =
             it->second.begin();
         rit != it->second.end(); rit++)
    {
      const ArrayTransformer::ChainRow& row = rit->second;
      EXPECT_EQ(SYMBOL, row.symbol.GetKind());
      EXPECT_FALSE(row.levels.empty());
      EXPECT_EQ(SYMBOL, row.baseArray.GetKind());
      EXPECT_EQ(SYMBOL, row.baseReadSymbol.GetKind());
      for (const ArrayTransformer::ChainLevel& lvl : row.levels)
      {
        EXPECT_FALSE(lvl.indexAnchor.IsNull());
        EXPECT_FALSE(lvl.valueAnchor.IsNull());
      }
    }
}

TEST(LazyWriteChainReads, few_reads_stay_eager)
{
  Harness s;
  EXPECT_EQ(0u, s.rowsAfterTransform(8, 3));
}

TEST(LazyWriteChainReads, shallow_chain_stays_eager)
{
  Harness s;
  EXPECT_EQ(0u, s.rowsAfterTransform(3, 8));
}

TEST(LazyWriteChainReads, flag_off_stays_eager)
{
  Harness s;
  s.mgr.UserFlags.lazy_write_reads = false;
  EXPECT_EQ(0u, s.rowsAfterTransform(8, 8));
}

TEST(LazyWriteChainReads, ackermannisation_stays_eager)
{
  Harness s;
  s.mgr.UserFlags.ackermannisation = true;
  EXPECT_EQ(0u, s.rowsAfterTransform(8, 8));
}

TEST(LazyWriteChainReads, registry_carries_rows_and_reports_touches)
{
  Harness s;
  ArrayTransformer::Registry persistent;
  const ASTNode f = s.chainFormula(8, 8);
  ArrayTransformer::TransformResult first =
      s.at.TransformFormulaWithRegistry(f, persistent);
  size_t rows = 0;
  for (ArrayTransformer::ChainReadsMap::const_iterator it =
           persistent.chains.begin();
       it != persistent.chains.end(); it++)
    rows += it->second.size();
  ASSERT_GT(rows, 0u);
  EXPECT_EQ(rows, first.touchedChains.size());
  // The batch tables stay clean of the persistent rows.
  EXPECT_TRUE(s.at.chainReads.empty());

  // A second transform reports its touched rows (hits, plus rows the
  // now-warmer popularity gate lets the previously-eager reads create).
  ArrayTransformer::TransformResult second =
      s.at.TransformFormulaWithRegistry(f, persistent);
  EXPECT_GE(second.touchedChains.size(), rows);
  size_t rowsAfter = 0;
  for (ArrayTransformer::ChainReadsMap::const_iterator it =
           persistent.chains.begin();
       it != persistent.chains.end(); it++)
    rowsAfter += it->second.size();
  EXPECT_GE(rowsAfter, rows);
}

} // namespace

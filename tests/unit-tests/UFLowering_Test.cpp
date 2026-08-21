/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
 *
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
********************************************************************/

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

#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFLowering.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

const LoweredApplicationRecord* findRecord(const LoweredApplicationView& view,
                                           const ASTNode& durable)
{
  for (const LoweredApplicationRecord& record : view.applications)
    if (record.durableHandle == durable)
      return &record;
  return NULL;
}

} // namespace

TEST(UFLowering, SharedNestedCompoundActualGetsOneCanonicalName)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* const context = manager.getUFContext();
  const SourceSort bv8 = SourceSort::bitVector(8);
  std::string diagnostic;
  const UFDecl* const f =
      context->declareFunction("f", {bv8}, bv8, &diagnostic);
  const UFDecl* const g =
      context->declareFunction("g", {bv8}, bv8, &diagnostic);
  ASSERT_NE(nullptr, f) << diagnostic;
  ASSERT_NE(nullptr, g) << diagnostic;

  NodeFactory* const factory = manager.defaultNodeFactory;
  const ASTNode x = manager.CreateSourceSymbol("x", bv8);
  const ASTNode one = manager.CreateBVConst(8, 1);
  const ASTNode inner = context->apply(f, {x}, &diagnostic);
  const ASTNode compound = factory->CreateTerm(BVPLUS, 8, inner, one);
  const ASTNode left = context->apply(f, {compound}, &diagnostic);
  const ASTNode right = context->apply(g, {compound}, &diagnostic);
  ASSERT_FALSE(inner.IsNull()) << diagnostic;
  ASSERT_FALSE(left.IsNull()) << diagnostic;
  ASSERT_FALSE(right.IsNull()) << diagnostic;

  const ASTNode root = factory->CreateNode(
      AND, factory->CreateNode(EQ, left, manager.CreateBVConst(8, 2)),
      factory->CreateNode(EQ, right, manager.CreateBVConst(8, 3)));
  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(41));

  ASSERT_EQ(3u, view.size());
  const LoweredApplicationRecord* const innerRecord = findRecord(view, inner);
  const LoweredApplicationRecord* const leftRecord = findRecord(view, left);
  const LoweredApplicationRecord* const rightRecord = findRecord(view, right);
  ASSERT_NE(nullptr, innerRecord);
  ASSERT_NE(nullptr, leftRecord);
  ASSERT_NE(nullptr, rightRecord);
  EXPECT_LT(innerRecord->stableOrder, leftRecord->stableOrder);
  EXPECT_LT(innerRecord->stableOrder, rightRecord->stableOrder);

  const ASTNode expectedLowered =
      factory->CreateTerm(BVPLUS, 8, innerRecord->resultSymbol, one);
  ASSERT_EQ(1u, leftRecord->loweredActuals.size());
  ASSERT_EQ(1u, rightRecord->loweredActuals.size());
  EXPECT_EQ(expectedLowered, leftRecord->loweredActuals[0]);
  EXPECT_EQ(expectedLowered, rightRecord->loweredActuals[0]);
  EXPECT_EQ(leftRecord->namedActuals[0], rightRecord->namedActuals[0]);
  EXPECT_EQ(1u, view.nameToTerm.size());
  EXPECT_EQ(1u, view.namingDefinitions.size());

  // The durable public tree is untouched, while both semantic forms enforce
  // the completed-root barrier through a shared, nested application DAG.
  EXPECT_TRUE(containsKind(view.publicRoot, UF_APPLY));
  EXPECT_FALSE(containsKind(expectedLowered, UF_APPLY));
  EXPECT_FALSE(containsKind(view.semanticRoot, UF_APPLY));
  EXPECT_FALSE(
      containsKind(view.semanticRootWithDefinitions(&manager), UF_APPLY));
}

TEST(UFLowering, ExplicitPostOrderHandlesDeepAdversarialSharedDag)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* const context = manager.getUFContext();
  const SourceSort bv8 = SourceSort::bitVector(8);
  std::string diagnostic;
  const UFDecl* const f =
      context->declareFunction("deep_f", {bv8}, bv8, &diagnostic);
  ASSERT_NE(nullptr, f) << diagnostic;

  // Every application below consumes the entire growing prefix, and that
  // prefix also contains the preceding application as a shared child. A
  // separate substitution walk per application is quadratic in this shape;
  // a single memoised post-order walk visits its O(depth) unique nodes once.
  const size_t depth = 4096;
  NodeFactory* const factory = manager.defaultNodeFactory;
  const ASTNode x = manager.CreateSourceSymbol("deep_x", bv8);
  ASTNode growing = x;
  ASTVec durable;
  durable.reserve(depth);
  for (size_t i = 0; i < depth; ++i)
  {
    const ASTNode application = context->apply(f, {growing}, &diagnostic);
    ASSERT_FALSE(application.IsNull()) << diagnostic;
    durable.push_back(application);
    if (i + 1 < depth)
      growing = factory->CreateTerm(BVPLUS, 8, growing, application);
  }

  const ASTNode root = factory->CreateNode(EQ, durable.back(), x);
  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(42));

  ASSERT_EQ(depth, view.size());
  ASSERT_EQ(depth, view.handleToResult.size());
  ASSERT_EQ(depth - 1, view.namingDefinitions.size());
  ASSERT_EQ(depth - 1, view.nameToTerm.size());
  for (size_t i = 0; i < depth; ++i)
  {
    EXPECT_EQ(i, view.applications[i].stableOrder);
    EXPECT_EQ(durable[i], view.applications[i].durableHandle);
    EXPECT_TRUE(context->isSolveScalar(view.applications[i].resultSymbol));
  }

  // Checking the deepest reconstructed actual exercises the whole rewritten
  // prefix. Neither it nor either semantic root may retain a durable apply.
  EXPECT_FALSE(
      containsKind(view.applications.back().loweredActuals[0], UF_APPLY));
  EXPECT_FALSE(containsKind(view.semanticRoot, UF_APPLY));
  EXPECT_FALSE(
      containsKind(view.semanticRootWithDefinitions(&manager), UF_APPLY));
}

TEST(UFLowering, EqualityOnlyResultsAreNarrowed)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  manager.UserFlags.uf_narrow_results = true;
  UFContext* const context = manager.getUFContext();
  const SourceSort bv256 = SourceSort::bitVector(256);
  std::string diagnostic;
  const UFDecl* const f =
      context->declareFunction("f", {bv256}, bv256, &diagnostic);
  ASSERT_NE(nullptr, f) << diagnostic;

  NodeFactory* const factory = manager.defaultNodeFactory;
  const ASTNode a = manager.CreateSourceSymbol("a", bv256);
  const ASTNode b = manager.CreateSourceSymbol("b", bv256);
  const ASTNode c = manager.CreateSourceSymbol("c", bv256);
  const ASTNode fa = context->apply(f, {a}, &diagnostic);
  const ASTNode fb = context->apply(f, {b}, &diagnostic);
  const ASTNode fc = context->apply(f, {c}, &diagnostic);
  ASSERT_FALSE(fa.IsNull()) << diagnostic;
  ASSERT_FALSE(fb.IsNull()) << diagnostic;
  ASSERT_FALSE(fc.IsNull()) << diagnostic;

  const ASTNode root = factory->CreateNode(
      AND, factory->CreateNode(EQ, fa, fb),
      factory->CreateNode(EQ, fb, fc));

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(50));

  ASSERT_EQ(3u, view.size());
  for (const LoweredApplicationRecord& record : view.applications)
    EXPECT_LT(record.resultSymbol.GetValueWidth(), 256u)
        << "result of " << record.durableHandle
        << " should have been narrowed";
}

TEST(UFLowering, NonEqualityUseBlocksNarrowing)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  manager.UserFlags.uf_narrow_results = true;
  UFContext* const context = manager.getUFContext();
  const SourceSort bv32 = SourceSort::bitVector(32);
  std::string diagnostic;
  const UFDecl* const f =
      context->declareFunction("f", {bv32}, bv32, &diagnostic);
  ASSERT_NE(nullptr, f) << diagnostic;

  NodeFactory* const factory = manager.defaultNodeFactory;
  const ASTNode a = manager.CreateSourceSymbol("a", bv32);
  const ASTNode b = manager.CreateSourceSymbol("b", bv32);
  const ASTNode fa = context->apply(f, {a}, &diagnostic);
  const ASTNode fb = context->apply(f, {b}, &diagnostic);
  ASSERT_FALSE(fa.IsNull()) << diagnostic;
  ASSERT_FALSE(fb.IsNull()) << diagnostic;

  const ASTNode root = factory->CreateNode(
      AND,
      factory->CreateNode(EQ,
          factory->CreateTerm(BVPLUS, 32, fa,
                              manager.CreateBVConst(32, 1)),
          fb));

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(51));

  ASSERT_EQ(2u, view.size());
  for (const LoweredApplicationRecord& record : view.applications)
    EXPECT_EQ(32u, record.resultSymbol.GetValueWidth())
        << "result of " << record.durableHandle
        << " should NOT have been narrowed";
}

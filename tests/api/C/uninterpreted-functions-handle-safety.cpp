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

#include "stp/c_interface.h"

// UF declarations can become inactive only through a parser scope today. Use
// the registry seam to create that state deterministically, then exercise it
// exclusively through the public C API.
#include "stp/STPManager/STP.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFDecl.h"

#include <cstdint>
#include <cstdlib>
#include <gtest/gtest.h>
#include <initializer_list>
#include <vector>

namespace
{

int apiErrors = 0;
void countAPIError(const char*) { ++apiErrors; }
void ignoreAPIError(const char*) {}

UFDeclHandle declareFunction(VC vc, const char* name,
                             std::initializer_list<unsigned> domainWidths,
                             unsigned codomainWidth)
{
  std::vector<Type> domain;
  domain.reserve(domainWidths.size());
  for (const unsigned width : domainWidths)
    domain.push_back(width == 0 ? vc_boolType(vc) : vc_bvType(vc, width));
  Type codomain = codomainWidth == 0 ? vc_boolType(vc)
                                     : vc_bvType(vc, codomainWidth);
  const UFDeclHandle declaration = vc_declareUninterpretedFunction(
      vc, name, domain.data(), domain.size(), codomain);
  for (const Type type : domain)
    vc_DeleteExpr(type);
  vc_DeleteExpr(codomain);
  return declaration;
}

TEST(UninterpretedFunctionsHandleSafety,
     InvalidAndInactiveDeclarationHandlesAreNonfatal)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  UFDeclHandle declaration = declareFunction(vc, "f", {8}, 8);
  ASSERT_NE(0u, declaration);
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  const Expr actuals[] = {x};

  UFDeclHandle impossible = UINT64_MAX;
  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(vc, impossible, actuals, 1));
  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(
                         vc, static_cast<UFDeclHandle>(
                                 reinterpret_cast<uintptr_t>(x)),
                         actuals, 1));

  stp::STP* engine = static_cast<stp::STP*>(vc);
  std::string diagnostic;
  const stp::UFDecl* internalDeclaration =
      engine->bm->getUFContext()->lookup("f");
  ASSERT_NE(nullptr, internalDeclaration);
  ASSERT_TRUE(engine->bm->getUFContext()->deactivate(
      internalDeclaration, &diagnostic));
  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(vc, declaration, actuals, 1));

  // Reset/pop-style deactivation frees the name but never recycles the
  // public declaration identity.  A fresh declaration works while the old
  // token remains stale even though both declarations have the same shape.
  UFDeclHandle replacement = declareFunction(vc, "f", {8}, 8);
  ASSERT_NE(0u, replacement);
  EXPECT_NE(declaration, replacement);
  Expr fresh =
      vc_applyUninterpretedFunction(vc, replacement, actuals, 1);
  EXPECT_NE(nullptr, fresh);
  EXPECT_EQ(nullptr,
            vc_applyUninterpretedFunction(vc, declaration, actuals, 1));
  EXPECT_GE(apiErrors, 4);

  vc_DeleteExpr(fresh);
  vc_DeleteExpr(x);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety,
     DestroyedAndCrossContextDeclarationsAndActualsAreNonfatal)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC owner = vc_createValidityChecker();
  VC other = vc_createValidityChecker();
  vc_setFlag(owner, 'u');
  vc_setFlag(other, 'u');
  UFDeclHandle fromOwner = declareFunction(owner, "owner_f", {8}, 8);
  UFDeclHandle fromOther = declareFunction(other, "other_f", {8}, 8);
  ASSERT_NE(0u, fromOwner);
  ASSERT_NE(0u, fromOther);

  Expr ownerX = vc_varExpr(owner, "owner_x", vc_bvType(owner, 8));
  Expr otherX = vc_varExpr(other, "other_x", vc_bvType(other, 8));
  const Expr otherActuals[] = {otherX};

  // Isolate declaration ownership from actual ownership: each call has only
  // one foreign input.
  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(other, fromOwner, otherActuals, 1));
  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(owner, fromOwner, otherActuals, 1));

  vc_DeleteExpr(ownerX);
  vc_Destroy(owner);

  // A declaration token whose owning checker is gone remains rejectable when
  // presented to a live checker; rejection must not inspect freed storage.
  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(other, fromOwner, otherActuals, 1));
  Expr validApplication = vc_applyUninterpretedFunction(other, fromOther, otherActuals, 1);
  EXPECT_NE(nullptr, validApplication);
  EXPECT_GE(apiErrors, 3);

  vc_DeleteExpr(validApplication);
  vc_DeleteExpr(otherX);
  vc_Destroy(other);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety, NullActualStorageIsNonfatal)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  UFDeclHandle declaration = declareFunction(vc, "f", {8}, 8);
  ASSERT_NE(0u, declaration);
  const Expr nullActual[] = {nullptr};

  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(vc, declaration, nullptr, 1));
  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(vc, declaration, nullActual, 1));
  EXPECT_EQ(2, apiErrors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety, InvalidActualPointerDoesNotCrash)
{
  EXPECT_EXIT(
      {
        vc_registerErrorHandler(ignoreAPIError);
        VC vc = vc_createValidityChecker();
        vc_setFlag(vc, 'u');
        UFDeclHandle declaration = declareFunction(vc, "f", {8}, 8);
        Expr invalid = reinterpret_cast<Expr>(static_cast<uintptr_t>(1));
        const Expr actuals[] = {invalid};
        Expr result = vc_applyUninterpretedFunction(vc, declaration, actuals, 1);
        if (result != nullptr)
          std::_Exit(2);
        vc_Destroy(vc);
        std::_Exit(0);
      },
      ::testing::ExitedWithCode(0), ".*");
}

TEST(UninterpretedFunctionsHandleSafety, DestroyedActualPointerDoesNotCrash)
{
  EXPECT_EXIT(
      {
        vc_registerErrorHandler(ignoreAPIError);
        VC vc = vc_createValidityChecker();
        vc_setFlag(vc, 'u');
        UFDeclHandle declaration = declareFunction(vc, "f", {8}, 8);
        Expr destroyed = vc_varExpr(vc, "x", vc_bvType(vc, 8));
        vc_DeleteExpr(destroyed);
        const Expr actuals[] = {destroyed};
        Expr result = vc_applyUninterpretedFunction(vc, declaration, actuals, 1);
        if (result != nullptr)
          std::_Exit(2);
        vc_Destroy(vc);
        std::_Exit(0);
      },
      ::testing::ExitedWithCode(0), ".*");
}

TEST(UninterpretedFunctionsHandleSafety,
     ActualFromDestroyedContextDoesNotCrash)
{
  EXPECT_EXIT(
      {
        vc_registerErrorHandler(ignoreAPIError);
        VC owner = vc_createValidityChecker();
        VC target = vc_createValidityChecker();
        vc_setFlag(owner, 'u');
        vc_setFlag(target, 'u');
        Expr destroyedOwnerActual =
            vc_varExpr(owner, "x", vc_bvType(owner, 8));
        UFDeclHandle declaration = declareFunction(target, "f", {8}, 8);
        vc_Destroy(owner);

        const Expr actuals[] = {destroyedOwnerActual};
        Expr result = vc_applyUninterpretedFunction(target, declaration, actuals, 1);
        if (result != nullptr)
          std::_Exit(2);
        vc_Destroy(target);
        std::_Exit(0);
      },
      ::testing::ExitedWithCode(0), ".*");
}

TEST(UninterpretedFunctionsHandleSafety,
     DestroyedApplicationValueHandleDoesNotCrash)
{
  EXPECT_EXIT(
      {
        vc_registerErrorHandler(ignoreAPIError);
        VC vc = vc_createValidityChecker();
        vc_setFlag(vc, 'u');
        UFDeclHandle declaration = declareFunction(vc, "f", {8}, 8);
        Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
        const Expr actuals[] = {x};
        Expr application = vc_applyUninterpretedFunction(vc, declaration, actuals, 1);
        vc_DeleteExpr(application);

        Expr value = vc_getUninterpretedFunctionValue(vc, application);
        if (value != nullptr)
          std::_Exit(2);
        vc_DeleteExpr(x);
        vc_Destroy(vc);
        std::_Exit(0);
      },
      ::testing::ExitedWithCode(0), ".*");
}

TEST(UninterpretedFunctionsHandleSafety,
     DeletedExpressionChurnLeavesTheContextUsable)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  vc_setInterfaceFlags(vc, EXPRDELETE, 0);
  UFDeclHandle declaration = declareFunction(vc, "f", {8}, 8);
  ASSERT_NE(0u, declaration);

  // Deleted raw Expr wrappers are released immediately rather than retained
  // as process-lifetime tombstones. Their pointer values may therefore be
  // reused; using a wrapper after vc_DeleteExpr follows the legacy invalid-
  // handle contract. Exercise enough live-registry insert/erase churn to catch
  // leaks in the supported ownership path, then prove the context still works.
  for (unsigned attempt = 0; attempt < 100000; ++attempt)
  {
    Expr argument = vc_bvConstExprFromInt(vc, 8, attempt & 0xffu);
    const Expr actuals[] = {argument};
    Expr application =
        vc_applyUninterpretedFunction(vc, declaration, actuals, 1);
    ASSERT_NE(nullptr, application);
    vc_DeleteExpr(application);
    vc_DeleteExpr(argument);
  }

  Expr argument = vc_bvConstExprFromInt(vc, 8, 7);
  const Expr actuals[] = {argument};
  Expr application =
      vc_applyUninterpretedFunction(vc, declaration, actuals, 1);
  EXPECT_NE(nullptr, application);
  EXPECT_EQ(0, apiErrors);
  vc_DeleteExpr(application);
  vc_DeleteExpr(argument);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety,
     DestroyedDeclarationCannotBecomeValidThroughAddressReuse)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;
  VC original = vc_createValidityChecker();
  vc_setFlag(original, 'u');
  UFDeclHandle stale = declareFunction(original, "old_f", {8}, 8);
  ASSERT_NE(0u, stale);
  vc_Destroy(original);

  // Churn both managers and declarations. Monotonic value identities never
  // reuse the stale token and require no process-lifetime heap tombstone.
  for (unsigned attempt = 0; attempt < 128; ++attempt)
  {
    VC live = vc_createValidityChecker();
    vc_setFlag(live, 'u');
    UFDeclHandle replacement =
        declareFunction(live, "replacement_f", {8}, 8);
    ASSERT_NE(0u, replacement);
    EXPECT_NE(stale, replacement);
    Expr x = vc_varExpr(live, "x", vc_bvType(live, 8));
    const Expr actuals[] = {x};
    EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(live, stale, actuals, 1));
    vc_DeleteExpr(x);
    vc_Destroy(live);
  }

  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety,
     NamespaceRejectionDoesNotDisplaceExistingBinding)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  UFDeclHandle declaration = declareFunction(vc, "f", {8}, 8);
  ASSERT_NE(0u, declaration);
  EXPECT_EQ(0u, declareFunction(vc, "f", {8}, 8));
  EXPECT_EQ(nullptr, vc_varExpr(vc, "f", vc_bvType(vc, 8)));

  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  const Expr actuals[] = {x};
  Expr application = vc_applyUninterpretedFunction(vc, declaration, actuals, 1);
  EXPECT_NE(nullptr, application);

  EXPECT_EQ(0u, declareFunction(vc, "x", {8}, 8));
  Expr xAgain = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  ASSERT_NE(nullptr, xAgain);
  EXPECT_EQ(getExprID(x), getExprID(xAgain));
  EXPECT_GE(apiErrors, 3);

  vc_DeleteExpr(xAgain);
  vc_DeleteExpr(application);
  vc_DeleteExpr(x);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety,
     BooleanApplicationUsesSourceSortEquality)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  UFDeclHandle predicate = declareFunction(vc, "predicate", {0}, 0);
  ASSERT_NE(0u, predicate);
  Expr argument = vc_trueExpr(vc);
  const Expr actuals[] = {argument};
  Expr application = vc_applyUninterpretedFunction(vc, predicate, actuals, 1);
  ASSERT_NE(nullptr, application);
  Expr expected = vc_falseExpr(vc);
  Expr equality = vc_eqExpr(vc, application, expected);
  ASSERT_NE(nullptr, equality);
  vc_assertFormula(vc, equality);
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_DeleteExpr(equality);
  vc_DeleteExpr(expected);
  vc_DeleteExpr(application);
  vc_DeleteExpr(argument);
  vc_Destroy(vc);
}

} // namespace

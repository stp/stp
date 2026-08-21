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

#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Globals/Globals.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"

#include <gtest/gtest.h>

using namespace stp;

TEST(UninterpretedFunctionsFrontend, IsDisabledByDefault)
{
  STPMgr manager;
  EXPECT_FALSE(manager.UserFlags.enable_uninterpreted_functions);

  std::string diagnostic;
  EXPECT_EQ(nullptr, manager.getUFContext()->declareFunction(
                      "f", {SourceSort::bitVector(8)},
                      SourceSort::bitVector(8), &diagnostic));
  EXPECT_EQ(0u, manager.getUFContext()->declarationCount());
  EXPECT_NE(std::string::npos, diagnostic.find("disabled"));
}

TEST(UninterpretedFunctionsFrontend, SignatureUsesRestrictedSourceSorts)
{
  EXPECT_THROW(UFSignature({}, SourceSort::boolean()), std::invalid_argument);
  EXPECT_THROW(UFSignature({SourceSort::bitVector(8)},
                           SourceSort::array(SourceSort::bitVector(8),
                                             SourceSort::bitVector(8))),
               std::invalid_argument);

  const UFSignature signature(
      {SourceSort::boolean(), SourceSort::bitVector(17)},
      SourceSort::bitVector(3));
  ASSERT_EQ(2u, signature.arity());
  EXPECT_EQ(SourceSort::Kind::Bool, signature.domain()[0].kind());
  EXPECT_EQ(17u, signature.domain()[1].bitVectorWidth());
  EXPECT_EQ(3u, signature.codomain().bitVectorWidth());

  // RoundingMode and FloatingPoint used to sit alongside the throwing rows
  // above. Both are now admitted in either position; the rows are kept,
  // inverted, so that a regression which re-rejected a sort fails here.
  const UFSignature mode({SourceSort::roundingMode()},
                         SourceSort::roundingMode());
  ASSERT_EQ(1u, mode.arity());
  EXPECT_EQ(SourceSort::Kind::RoundingMode, mode.domain()[0].kind());
  EXPECT_EQ(SourceSort::Kind::RoundingMode, mode.codomain().kind());
  EXPECT_EQ(5u, mode.codomain().packedWidth());

  const UFSignature floats({SourceSort::floatingPoint(8, 24)},
                           SourceSort::floatingPoint(11, 53));
  ASSERT_EQ(1u, floats.arity());
  EXPECT_EQ(SourceSort::Kind::FloatingPoint, floats.domain()[0].kind());
  EXPECT_EQ(SourceSort::Kind::FloatingPoint, floats.codomain().kind());

  // Admitted at its own sort, but never *solved* at it: a float is compared
  // as its canonical packed carrier, because SMT-LIB's = on floats identifies
  // every NaN and byte equality does not.
  EXPECT_EQ(SourceSort::bitVector(32),
            UFSignature::loweringSort(floats.domain()[0]));
  EXPECT_EQ(SourceSort::bitVector(64),
            UFSignature::loweringSort(floats.codomain()));
  // Every other admitted sort is solved exactly as declared.
  EXPECT_EQ(SourceSort::boolean(),
            UFSignature::loweringSort(SourceSort::boolean()));
  EXPECT_EQ(SourceSort::roundingMode(),
            UFSignature::loweringSort(SourceSort::roundingMode()));
  EXPECT_EQ(SourceSort::bitVector(17),
            UFSignature::loweringSort(SourceSort::bitVector(17)));
}

TEST(UninterpretedFunctionsFrontend,
     UnsupportedDirectSignaturesMutateNoRegistry)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  const SourceSort bv8 = SourceSort::bitVector(8);
  const SourceSort array = SourceSort::array(bv8, bv8);
  std::string diagnostic;

  EXPECT_EQ(nullptr,
            context->declareFunction("empty", {}, bv8, &diagnostic));
  EXPECT_EQ("uninterpreted functions: declaration of empty: a zero-arity "
            "declaration is an ordinary symbol, not an uninterpreted function",
            diagnostic);
  // The RoundingMode and FloatingPoint rows that used to sit here are now
  // admitted; they moved to the positive tests below, where the registry is
  // expected to change rather than stay empty.
  EXPECT_EQ(nullptr,
            context->declareFunction("array", {array}, bv8, &diagnostic));
  EXPECT_EQ("uninterpreted functions: declaration of array: unsupported "
            "domain sort (Array (_ BitVec 8) (_ BitVec 8)) at argument 0 "
            "(only Bool, RoundingMode, FloatingPoint and nonzero-width "
            "bit-vector sorts are supported)",
            diagnostic);
  EXPECT_EQ(nullptr, context->declareFunction(
                         "unknown", {SourceSort::unknown()}, bv8,
                         &diagnostic));
  EXPECT_EQ(nullptr,
            context->declareFunction("result", {bv8}, array, &diagnostic));
  EXPECT_EQ("uninterpreted functions: declaration of result: unsupported "
            "result sort (Array (_ BitVec 8) (_ BitVec 8)) (only Bool, "
            "RoundingMode, FloatingPoint and nonzero-width bit-vector "
            "sorts are supported)",
            diagnostic);
  EXPECT_EQ(0u, context->declarationCount());
  EXPECT_EQ(0u, context->registeredApplicationCount());
}

TEST(UninterpretedFunctionsFrontend, RoundingModeSignaturesAreAdmitted)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  const SourceSort rm = SourceSort::roundingMode();
  const SourceSort bv8 = SourceSort::bitVector(8);
  std::string diagnostic;

  const UFDecl* toMode =
      context->declareFunction("toMode", {bv8}, rm, &diagnostic);
  ASSERT_NE(nullptr, toMode) << diagnostic;
  const UFDecl* fromMode =
      context->declareFunction("fromMode", {rm}, bv8, &diagnostic);
  ASSERT_NE(nullptr, fromMode) << diagnostic;
  EXPECT_EQ(2u, context->declarationCount());

  // Declaring a RoundingMode-sorted identity is enough to make the manager
  // report the floating-point theory, which is what routes the query to
  // FpTotalise and to the mode-aware model printers.
  EXPECT_TRUE(manager.has_floating_point_theory);

  const ASTNode x = manager.CreateSourceSymbol("x", bv8);
  const ASTNode application = context->apply(toMode, {x}, &diagnostic);
  ASSERT_FALSE(application.IsNull()) << diagnostic;
  EXPECT_EQ(UF_APPLY, application.GetKind());
  // The carrier is the packed one -- five bits -- while the source sort stays
  // RoundingMode. BVTypeCheck's UF_APPLY rule enforces exactly this pairing.
  EXPECT_EQ(SourceSort::Kind::RoundingMode,
            application.GetSourceSort().kind());
  EXPECT_EQ(BITVECTOR_TYPE, application.GetType());
  EXPECT_EQ(5u, application.GetValueWidth());
  EXPECT_TRUE(BVTypeCheck(application));
}

TEST(UninterpretedFunctionsFrontend, DurableApplicationsAreTypedAndHashConsed)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();

  std::string diagnostic;
  const UFDecl* bv = context->declareFunction(
      "f", {SourceSort::bitVector(8), SourceSort::boolean()},
      SourceSort::bitVector(16), &diagnostic);
  const UFDecl* pred = context->declareFunction(
      "p", {SourceSort::bitVector(8)}, SourceSort::boolean(), &diagnostic);
  ASSERT_NE(nullptr, bv) << diagnostic;
  ASSERT_NE(nullptr, pred) << diagnostic;

  const ASTNode x =
      manager.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode b =
      manager.CreateSourceSymbol("b", SourceSort::boolean());
  const ASTNode app = context->apply(bv, {x, b}, &diagnostic);
  const ASTNode again = context->apply(bv, {x, b}, &diagnostic);
  const ASTNode boolApp = context->apply(pred, {x}, &diagnostic);

  EXPECT_EQ(UF_APPLY, app.GetKind());
  EXPECT_EQ(app, again);
  EXPECT_EQ(bv->identityNode(), app[0]);
  EXPECT_EQ(x, app[1]);
  EXPECT_EQ(b, app[2]);
  EXPECT_EQ(SourceSort::bitVector(16), app.GetSourceSort());
  EXPECT_EQ(BITVECTOR_TYPE, app.GetType());
  EXPECT_EQ(16u, app.GetValueWidth());
  EXPECT_EQ(SourceSort::boolean(), boolApp.GetSourceSort());
  EXPECT_EQ(BOOLEAN_TYPE, boolApp.GetType());
  EXPECT_TRUE(context->isRegisteredApplication(app));
  EXPECT_EQ(2u, context->registeredApplicationCount());
  EXPECT_TRUE(BVTypeCheck(app));
  EXPECT_TRUE(BVTypeCheck(boolApp));
}

TEST(UninterpretedFunctionsFrontend, FailedApplicationsRegisterNothing)
{
  STPMgr first;
  STPMgr second;
  first.UserFlags.enable_uninterpreted_functions = true;
  second.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = first.getUFContext();
  std::string diagnostic;
  const UFDecl* declaration = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  ASSERT_NE(nullptr, declaration);

  const ASTNode wrong =
      first.CreateSourceSymbol("wrong", SourceSort::boolean());
  const ASTNode foreign =
      second.CreateSourceSymbol("foreign", SourceSort::bitVector(8));
  EXPECT_EQ(UNDEFINED,
            context->apply(declaration, ASTVec(), &diagnostic).GetKind());
  EXPECT_EQ("uninterpreted functions: f expects 1 argument but was applied "
            "to 0",
            diagnostic);
  EXPECT_EQ(UNDEFINED,
            context->apply(declaration, {wrong}, &diagnostic).GetKind());
  EXPECT_EQ("uninterpreted functions: argument 0 of f has sort Bool but the "
            "declaration requires (_ BitVec 8)",
            diagnostic);
  EXPECT_EQ(UNDEFINED,
            context->apply(declaration, {foreign}, &diagnostic).GetKind());
  EXPECT_EQ("uninterpreted functions: argument 0 of f belongs to another "
            "context",
            diagnostic);
  EXPECT_EQ(0u, context->registeredApplicationCount());

  ASSERT_TRUE(context->deactivate(declaration, &diagnostic));
  const ASTNode x =
      first.CreateSourceSymbol("x", SourceSort::bitVector(8));
  EXPECT_EQ(UNDEFINED,
            context->apply(declaration, {x}, &diagnostic).GetKind());
  EXPECT_EQ(0u, context->registeredApplicationCount());
}

TEST(UninterpretedFunctionsFrontend, SubstitutionRebuildsDurableApplication)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* declaration = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  ASSERT_NE(nullptr, declaration);
  const ASTNode formal =
      manager.CreateSourceSymbol("formal", SourceSort::bitVector(8));
  const ASTNode actual = manager.CreateBVConst(8, 42);
  const ASTNode generic = context->apply(declaration, {formal}, &diagnostic);

  ASTNodeMap substitutions;
  substitutions.insert(std::make_pair(formal, actual));
  ASTNodeMap cache;
  const ASTNode specialized = SubstitutionMap::replace(
      generic, substitutions, cache, manager.defaultNodeFactory);

  ASSERT_EQ(UF_APPLY, specialized.GetKind());
  EXPECT_NE(generic, specialized);
  EXPECT_EQ(declaration->identityNode(), specialized[0]);
  EXPECT_EQ(actual, specialized[1]);
  EXPECT_TRUE(context->isRegisteredApplication(specialized));
}

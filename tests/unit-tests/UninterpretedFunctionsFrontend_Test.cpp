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
#include "stp/Parser/parser.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/cpp_interface.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFLowering.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

// Lowering order follows the post-order walk, so a test that adds
// applications to reach a comparable declaration should not also have to
// predict where each one lands.
const LoweredApplicationRecord* recordFor(const LoweredApplicationView& view,
                                          const ASTNode& durableHandle)
{
  for (const LoweredApplicationRecord& record : view.applications)
    if (record.durableHandle == durableHandle)
      return &record;
  return NULL;
}

} // namespace

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

  // A sort declared by declare-sort is solved at its own sort, like a rounding
  // mode and unlike a float: equality is its only operation and bit equality on
  // its carrier is exactly that. Mapping it to its carrier here would compile,
  // pass everything else, and make models print at the carrier again.
  const SourceSort declared = registerUninterpretedSort("Loose", 16);
  EXPECT_TRUE(UFSignature::isSupportedSort(declared));
  EXPECT_EQ(declared, UFSignature::loweringSort(declared));
  EXPECT_NE(SourceSort::bitVector(16), UFSignature::loweringSort(declared));
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
            "(only Bool, RoundingMode, FloatingPoint, nonzero-width "
            "bit-vector sorts and sorts introduced by declare-sort are "
            "supported)",
            diagnostic);
  EXPECT_EQ(nullptr, context->declareFunction(
                         "unknown", {SourceSort::unknown()}, bv8,
                         &diagnostic));
  EXPECT_EQ(nullptr,
            context->declareFunction("result", {bv8}, array, &diagnostic));
  EXPECT_EQ("uninterpreted functions: declaration of result: unsupported "
            "result sort (Array (_ BitVec 8) (_ BitVec 8)) (only Bool, "
            "RoundingMode, FloatingPoint, nonzero-width bit-vector sorts "
            "and sorts introduced by declare-sort are supported)",
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

TEST(UninterpretedFunctionsFrontend,
     MalformedParserApplicationRejectsWholeCommandAndContinues)
{
  STPMgr manager;
  Cpp_interface interface(manager, manager.defaultNodeFactory);
  STPMgr* const savedManager = GlobalParserBM;
  Cpp_interface* const savedInterface = GlobalParserInterface;
  GlobalParserBM = &manager;
  GlobalParserInterface = &interface;
  interface.startup();
  manager.UserFlags.enable_uninterpreted_functions = true;

  // The first assertion has a valid application followed by one with the
  // wrong arity. Its valid prefix and parser-side carrier must both roll back:
  // neither may become an assertion or a registered durable application.
  // Parsing must nevertheless continue to the independent assertion.
  const char* const input = R"(
    (set-logic QF_UFBV)
    (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
    (declare-const x (_ BitVec 8))
    (assert (and (= (f x) x) (= (f x x) x)))
    (assert (= x #x00))
  )";
  SMT2ScanString(input);
  EXPECT_EQ(0, SMT2Parse());
  smt2lex_destroy();

  const std::size_t applicationCount =
      manager.getUFContext()->registeredApplicationCount();
  const std::size_t declarationCount =
      manager.getUFContext()->declarationCount();
  const bool xIsUF = manager.getUFContext()->lookup("x") != nullptr;
  const ASTVec assertions = manager.GetAsserts();
  const bool containsApplication =
      !assertions.empty() && containsKind(assertions[0], UF_APPLY);
  const bool rejected = interface.currentCommandRejected();

  GlobalParserBM = savedManager;
  GlobalParserInterface = savedInterface;

  EXPECT_EQ(0u, applicationCount);
  EXPECT_EQ(1u, declarationCount);
  EXPECT_FALSE(xIsUF);
  ASSERT_EQ(1u, assertions.size());
  EXPECT_FALSE(containsApplication);
  EXPECT_FALSE(rejected);
}

TEST(UninterpretedFunctionsFrontend,
     MalformedFormalCannotLeakLexerOrTemporaryStateAcrossParses)
{
  STPMgr manager;
  Cpp_interface interface(manager, manager.defaultNodeFactory);
  STPMgr* const savedManager = GlobalParserBM;
  Cpp_interface* const savedInterface = GlobalParserInterface;
  GlobalParserBM = &manager;
  GlobalParserInterface = &interface;
  interface.startup();
  manager.UserFlags.enable_uninterpreted_functions = true;

  // The empty formal reaches function_param_open but supplies no identifier,
  // leaving the lexer's next-name expectation armed unless parse-abort cleanup
  // explicitly clears it.
  SMT2ScanString(R"(
    (set-logic QF_UFBV)
    (define-fun broken (() Bool) Bool true)
  )");
  EXPECT_NE(0, SMT2Parse());
  smt2lex_destroy();

  // A second parse on the same interface must start a fresh command and may
  // declare/use another formal normally.
  SMT2ScanString(R"(
    (define-fun good ((fresh Bool)) Bool fresh)
    (declare-const witness Bool)
    (assert (good witness))
  )");
  EXPECT_EQ(0, SMT2Parse());
  smt2lex_destroy();

  const ASTVec assertions = manager.GetAsserts();

  GlobalParserBM = savedManager;
  GlobalParserInterface = savedInterface;

  ASSERT_EQ(1u, assertions.size());
  EXPECT_EQ(SYMBOL, assertions[0].GetKind());
  EXPECT_STREQ("witness", assertions[0].GetName());
  EXPECT_EQ(SourceSort::boolean(), assertions[0].GetSourceSort());
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

TEST(UninterpretedFunctionsFrontend,
     CompletedRootLoweringBuildsOnlyReachableNestedClosure)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* declaration = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  ASSERT_NE(nullptr, declaration) << diagnostic;

  const ASTNode x =
      manager.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode inner = context->apply(declaration, {x}, &diagnostic);
  const ASTNode outer = context->apply(declaration, {inner}, &diagnostic);
  const ASTNode unreachable = context->apply(
      declaration, {manager.CreateBVConst(8, 9)}, &diagnostic);
  ASSERT_FALSE(unreachable.IsNull());
  const ASTNode root =
      manager.defaultNodeFactory->CreateNode(EQ, outer, x);

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(17));

  ASSERT_EQ(2u, view.size());
  EXPECT_EQ(root, view.publicRoot);
  EXPECT_FALSE(containsKind(view.semanticRoot, UF_APPLY));
  EXPECT_TRUE(view.handleToResult.find(inner) != view.handleToResult.end());
  EXPECT_TRUE(view.handleToResult.find(outer) != view.handleToResult.end());
  EXPECT_TRUE(view.handleToResult.find(unreachable) ==
              view.handleToResult.end());
  EXPECT_EQ(inner, view.applications[0].durableHandle);
  EXPECT_EQ(outer, view.applications[1].durableHandle);
  ASSERT_EQ(1u, view.applications[1].namedActuals.size());
  EXPECT_EQ(view.applications[0].resultSymbol,
            view.applications[1].namedActuals[0]);
  EXPECT_TRUE(context->isProtected(view.applications[0].resultSymbol));
  EXPECT_TRUE(context->isProtected(view.applications[1].resultSymbol));
  EXPECT_TRUE(context->isSolveScalar(view.applications[0].resultSymbol));
  EXPECT_TRUE(context->isSolveScalar(view.applications[1].resultSymbol));
}

TEST(UninterpretedFunctionsFrontend,
     CompletedRootLoweringNamesEachComplexActualOnce)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* f = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  const UFDecl* g = context->declareFunction(
      "g", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  ASSERT_NE(nullptr, f);
  ASSERT_NE(nullptr, g);
  const ASTNode x =
      manager.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode one = manager.CreateBVConst(8, 1);
  const ASTNode complex = manager.defaultNodeFactory->CreateTerm(
      BVPLUS, 8, x, one);
  const ASTNode fx = context->apply(f, {complex}, &diagnostic);
  const ASTNode gx = context->apply(g, {complex}, &diagnostic);
  // A compound actual is named only where a congruence lemma could mention
  // it, so each declaration needs a second application; both are given a leaf
  // actual, which introduces no further name.
  const ASTNode fLeaf = context->apply(f, {x}, &diagnostic);
  const ASTNode gLeaf = context->apply(g, {one}, &diagnostic);
  const ASTNode root = manager.defaultNodeFactory->CreateNode(
      AND, manager.defaultNodeFactory->CreateNode(EQ, fx, gx),
      manager.defaultNodeFactory->CreateNode(EQ, fLeaf, gLeaf));

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(18));
  ASSERT_EQ(4u, view.size());
  ASSERT_EQ(1u, view.namingDefinitions.size());
  ASSERT_EQ(1u, view.nameToTerm.size());
  const LoweredApplicationRecord* const fRecord = recordFor(view, fx);
  const LoweredApplicationRecord* const gRecord = recordFor(view, gx);
  ASSERT_NE(nullptr, fRecord);
  ASSERT_NE(nullptr, gRecord);
  EXPECT_TRUE(fRecord->observableArguments);
  EXPECT_TRUE(gRecord->observableArguments);
  EXPECT_EQ(fRecord->namedActuals[0], gRecord->namedActuals[0]);
  EXPECT_TRUE(context->isProtected(fRecord->namedActuals[0]));
  EXPECT_TRUE(context->isSolveScalar(fRecord->namedActuals[0]));
  EXPECT_FALSE(containsKind(view.semanticRootWithDefinitions(&manager),
                            UF_APPLY));

  // The ordinary substitution funnel must not delete either a UF result or
  // its argument-name definition after the lowering barrier.
  SubstitutionMap substitutions(&manager);
  EXPECT_FALSE(context->activeInSolve());
  {
    UFContext::SolveScope scope(context);
    EXPECT_TRUE(context->activeInSolve());
    EXPECT_FALSE(substitutions.UpdateSolverMap(fRecord->resultSymbol,
                                               manager.CreateBVConst(8, 3)));
    EXPECT_FALSE(
        substitutions.UpdateSolverMap(fRecord->namedActuals[0], complex));
  }
  EXPECT_FALSE(context->activeInSolve());
}

TEST(UninterpretedFunctionsFrontend, LoneApplicationLeavesCompoundActualUnnamed)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* f = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8), &diagnostic);
  ASSERT_NE(nullptr, f);
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode y = manager.CreateSourceSymbol("y", SourceSort::bitVector(8));
  const ASTNode complex =
      manager.defaultNodeFactory->CreateTerm(BVPLUS, 8, x, y);
  const ASTNode fx = context->apply(f, {complex}, &diagnostic);
  const ASTNode root = manager.defaultNodeFactory->CreateNode(
      EQ, fx, manager.CreateBVConst(8, 3));

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(30));
  ASSERT_EQ(1u, view.size());
  // No second application of f exists, so no congruence lemma can ever equate
  // this actual with anything: naming it would only drag BVPLUS into the
  // bit-blast where nothing can observe it.
  EXPECT_FALSE(view.applications[0].observableArguments);
  EXPECT_TRUE(view.applications[0].namedActuals.empty());
  EXPECT_TRUE(view.namingDefinitions.empty());
  EXPECT_TRUE(view.nameToTerm.empty());
  EXPECT_FALSE(containsKind(view.semanticRootWithDefinitions(&manager),
                            BVPLUS));

  // The result symbol is still a protected solve scalar: it stands in for the
  // application in the formula and carries the certified value.
  EXPECT_TRUE(context->isProtected(view.applications[0].resultSymbol));
  EXPECT_TRUE(context->isSolveScalar(view.applications[0].resultSymbol));
}
TEST(UninterpretedFunctionsFrontend, LoneApplicationReusesAnExistingName)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* f = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8), &diagnostic);
  const UFDecl* g = context->declareFunction(
      "g", {SourceSort::bitVector(8)}, SourceSort::bitVector(8), &diagnostic);
  ASSERT_NE(nullptr, f);
  ASSERT_NE(nullptr, g);
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode y = manager.CreateSourceSymbol("y", SourceSort::bitVector(8));
  const ASTNode complex =
      manager.defaultNodeFactory->CreateTerm(BVPLUS, 8, x, y);
  // f is comparable and names `complex`; g's single application shares that
  // term, so it costs nothing to keep g readable too.
  const ASTNode fComplex = context->apply(f, {complex}, &diagnostic);
  const ASTNode fLeaf = context->apply(f, {x}, &diagnostic);
  const ASTNode gComplex = context->apply(g, {complex}, &diagnostic);
  const ASTNode root = manager.defaultNodeFactory->CreateNode(
      AND, manager.defaultNodeFactory->CreateNode(EQ, fComplex, fLeaf),
      manager.defaultNodeFactory->CreateNode(EQ, gComplex,
                                             manager.CreateBVConst(8, 3)));

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(31));
  ASSERT_EQ(3u, view.size());
  ASSERT_EQ(1u, view.namingDefinitions.size());
  const LoweredApplicationRecord* const fRecord = recordFor(view, fComplex);
  const LoweredApplicationRecord* const gRecord = recordFor(view, gComplex);
  ASSERT_NE(nullptr, fRecord);
  ASSERT_NE(nullptr, gRecord);
  EXPECT_TRUE(gRecord->observableArguments);
  ASSERT_EQ(1u, gRecord->namedActuals.size());
  EXPECT_EQ(fRecord->namedActuals[0], gRecord->namedActuals[0]);
}

TEST(UninterpretedFunctionsFrontend, BooleanLoweringRetainsBoolSourceSort)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* pred = context->declareFunction(
      "p", {SourceSort::boolean()}, SourceSort::boolean(), &diagnostic);
  ASSERT_NE(nullptr, pred);
  const ASTNode a =
      manager.CreateSourceSymbol("a", SourceSort::boolean());
  const ASTNode b =
      manager.CreateSourceSymbol("b", SourceSort::boolean());
  const ASTNode complex =
      manager.defaultNodeFactory->CreateNode(XOR, a, b);
  const ASTNode app = context->apply(pred, {complex}, &diagnostic);
  // Two applications, so the compound actual earns a name to be equated in.
  const ASTNode leafApp = context->apply(pred, {a}, &diagnostic);
  const ASTNode root =
      manager.defaultNodeFactory->CreateNode(AND, app, leafApp);

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(19));
  ASSERT_EQ(2u, view.size());
  ASSERT_EQ(1u, view.namingDefinitions.size());
  const LoweredApplicationRecord* const record = recordFor(view, app);
  ASSERT_NE(nullptr, record);
  EXPECT_EQ(SourceSort::boolean(), record->resultSymbol.GetSourceSort());
  EXPECT_EQ(SourceSort::boolean(), record->namedActuals[0].GetSourceSort());
  EXPECT_EQ(IFF, view.namingDefinitions[0].GetKind());
}

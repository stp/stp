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

#include "stp/UninterpretedFunctions/UFModel.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFRefinement.h"
#include "extlib-constbv/constantbv.h"
#include <algorithm>
#include <cctype>
#include <sstream>

namespace stp
{

namespace
{

bool validQuotedSymbol(const std::string& name)
{
  // SMT-LIB quoted symbols have no escape for either delimiter character.
  // Parser declarations have already stripped their surrounding bars.
  for (const unsigned char c : name)
    if (c == '|' || c == '\\' || !std::isprint(c))
      return false;
  return true;
}

void printQuotedSymbol(std::ostream& os, const std::string& name)
{
  if (!validQuotedSymbol(name))
    FatalError("UF model contains an external name that cannot be rendered "
               "as an SMT-LIB2 quoted symbol");
  os << '|' << name << '|';
}

void printSort(std::ostream& os, STPMgr* manager, const SourceSort& sort)
{
  if (!UFSignature::isSupportedSort(sort))
    FatalError("UF model tried to print an unsupported SourceSort");
  // A signature is the one way a declared sort reaches a model without any
  // element of it being named -- a predicate over an opaque sort -- and the
  // model still has to declare it.
  manager->noteUninterpretedSortPrinted(sort);
  os << sourceSortToSMTLib(sort);
}

// Seed values are stored at the lowering sort; `declared` is the signature
// sort they will be published at. The two differ only for FloatingPoint
// (and for narrowed bit-vector results).
void requireValueSort(const UFConcreteValue& value,
                      const SourceSort& declared)
{
  const SourceSort expected = UFSignature::loweringSort(declared);
  if (value.sort() == expected)
    return;
  if (expected.kind() == SourceSort::Kind::BitVector &&
      value.sort().kind() == SourceSort::Kind::BitVector &&
      value.sort().bitVectorWidth() <= expected.bitVectorWidth())
    return;
  FatalError("UF model seed contains a value at the wrong SourceSort");
}

void printValue(std::ostream& os, STPMgr* manager,
                const UFConcreteValue& value, const SourceSort& declared)
{
  const ASTNode constant = UFModel::concreteValue(manager, value, declared);
  if (declared.kind() == SourceSort::Kind::Bool)
  {
    os << (constant.GetKind() == TRUE ? "true" : "false");
    return;
  }
  // A rounding mode denotes one of five modes, not a 5-bit number, so the
  // define-fun this text goes into has to name the mode; a bit-vector
  // literal there is not a term of the sort. concreteValue has already
  // refused any carrier that names none.
  if (declared.kind() == SourceSort::Kind::RoundingMode)
  {
    const char* name = printer::roundingModeName(constant.GetUnsignedConst());
    if (name == NULL)
      FatalError("UF model holds a RoundingMode value that denotes no mode");
    os << name;
    return;
  }
  // Likewise a float: (fp #bS #bE #bM) at the declared format, not the packed
  // carrier the checker solved it as.
  if (declared.kind() == SourceSort::Kind::FloatingPoint)
  {
    printer::outputFloatingPointSMTLIB2(constant, os, constant);
    return;
  }
  // An element of a declared sort has no literal at all. It gets a name, and
  // the model's preamble declares it; a carrier pattern here would be a
  // bit-vector literal where a term of the sort belongs, which is the same
  // mistake as printing a rounding mode's five bits.
  if (declared.kind() == SourceSort::Kind::Uninterpreted)
  {
    os << '|' << manager->uninterpretedElementName(declared, constant) << '|';
    return;
  }
  printer::outputBitVecSMTLIB2(constant, os);
}

void printCondition(std::ostream& os, STPMgr* manager,
                    const UFSignature& signature,
                    const UFConcreteTuple& arguments)
{
  if (arguments.size() != signature.arity())
    FatalError("UF model case has the wrong arity");
  if (arguments.size() > 1)
    os << "(and ";
  for (size_t i = 0; i < arguments.size(); ++i)
  {
    if (i != 0)
      os << ' ';
    requireValueSort(arguments[i], signature.domain()[i]);
    os << "(= x" << i << ' ';
    printValue(os, manager, arguments[i], signature.domain()[i]);
    os << ')';
  }
  if (arguments.size() > 1)
    os << ')';
}

// A floating-point actual as the checker would have bucketed it: its
// canonical packed bits.
//
// The value arrives either as a float constant or as the bare carrier the SAT
// assignment materialised, so it is lifted to the declared sort first --
// which is where NaN gets quotiented, since STPMgr::CreateFPConst interns
// every NaN pattern as the one canonical quiet NaN -- and then taken back
// through the same FP_TO_IEEE_BV boundary UF lowering puts on the argument
// side. Over a constant that folds rather than building a circuit; a null
// return means it did not, which the caller reports rather than guessing.
ASTNode canonicalConstant(STPMgr* manager, const ASTNode& constant,
                          const SourceSort& declared)
{
  if (constant.GetKind() != BVCONST ||
      constant.GetValueWidth() != declared.packedWidth())
    return ASTNode();
  const ASTNode packed = manager->defaultNodeFactory->CreateTerm(
      FP_TO_IEEE_BV, declared.packedWidth(),
      manager->LiftSourceValue(constant, declared));
  return packed.GetKind() == BVCONST ? packed : ASTNode();
}

bool seedFunctionBefore(const UFFunctionModelSeed* left,
                        const UFFunctionModelSeed* right)
{
  if (left == NULL || right == NULL || left->declaration == NULL ||
      right->declaration == NULL)
    return left < right;
  if (left->declaration->name() != right->declaration->name())
    return left->declaration->name() < right->declaration->name();
  return left->declaration->id() < right->declaration->id();
}

} // namespace

ASTNode UFModel::concreteValue(STPMgr* manager,
                               const UFConcreteValue& value)
{
  if (manager == NULL)
    FatalError("UF concrete-value conversion has no manager");
  const SourceSort& sort = value.sort();
  if (sort.kind() == SourceSort::Kind::Bool)
    return value.booleanValue() ? manager->ASTTrue : manager->ASTFalse;
  if (!UFSignature::isSupportedSort(sort))
    FatalError("UF concrete-value conversion received an unsupported sort");

  const unsigned width = sort.packedWidth();
  const std::vector<uint8_t>& bytes = value.bytes();
  if (bytes.size() != (width + 7) / 8)
    FatalError("UF concrete-value conversion received malformed bytes");
  CBV bits = CONSTANTBV::BitVector_Create(width, true);
  CONSTANTBV::BitVector_Empty(bits);
  for (unsigned i = 0; i < width; ++i)
    if ((bytes[i / 8] & static_cast<uint8_t>(1u << (i % 8))) != 0)
      CONSTANTBV::BitVector_Bit_On(bits, i);
  const ASTNode carrier = manager->CreateBVConst(bits, width); // consumes bits
  // The checker's currency is the packed carrier; a model has to hand back a
  // term of the declared sort. LiftSourceValue is the funnel that already
  // does this for every other model boundary, and it refuses a carrier that
  // denotes nothing -- an all-zero "rounding mode", say -- rather than
  // publishing it.
  return manager->LiftSourceValue(carrier, sort);
}

ASTNode UFModel::concreteValue(STPMgr* manager, const UFConcreteValue& value,
                               const SourceSort& declared)
{
  const SourceSort expected = UFSignature::loweringSort(declared);
  const bool narrowedBV =
      expected.kind() == SourceSort::Kind::BitVector &&
      value.sort().kind() == SourceSort::Kind::BitVector &&
      value.sort().bitVectorWidth() < expected.bitVectorWidth();
  if (value.sort() != expected && !narrowedBV)
    FatalError("UF concrete-value conversion received a value at the wrong "
               "lowering sort");
  if (narrowedBV)
  {
    const unsigned targetWidth = expected.bitVectorWidth();
    std::vector<uint8_t> extended((targetWidth + 7) / 8, 0);
    const std::vector<uint8_t>& src = value.bytes();
    for (size_t i = 0; i < src.size() && i < extended.size(); ++i)
      extended[i] = src[i];
    const UFConcreteValue widened =
        UFConcreteValue::bitVector(targetWidth, extended);
    return concreteValue(manager, widened);
  }
  const ASTNode solved = concreteValue(manager, value);
  if (declared.kind() != SourceSort::Kind::FloatingPoint)
    return solved;
  return manager->LiftSourceValue(solved, declared);
}

bool UFModel::evaluateApplication(STPMgr* manager,
                                  const UFTheoryAdapter* adapter,
                                  const ASTNode& durableHandle,
                                  ASTNode& value,
                                  std::string& diagnostic)
{
  value = ASTNode();
  if (manager == NULL || durableHandle.IsNull() ||
      !durableHandle.IsOwnedBy(manager))
  {
    diagnostic = "uninterpreted-function application belongs to another "
                 "context or is invalid";
    return false;
  }
  UFContext* context = manager->getUFContextIfAny();
  if (context == NULL ||
      !context->isRegisteredApplication(durableHandle))
  {
    diagnostic = "expression is not a registered durable "
                 "uninterpreted-function application";
    return false;
  }
  if (!context->isActiveApplication(durableHandle))
  {
    diagnostic = "uninterpreted-function application is stale or inactive";
    return false;
  }
  if (adapter == NULL || !adapter->hasCertifiedModel())
  {
    diagnostic = "no certified uninterpreted-function model is available";
    return false;
  }
  UFConcreteValue concrete;
  if (!adapter->lookupCertifiedApplication(durableHandle, concrete))
  {
    diagnostic = "uninterpreted-function application was not active in the "
                 "certified solve";
    return false;
  }
  const SourceSort declared = durableHandle.GetSourceSort();
  const SourceSort expected = UFSignature::loweringSort(declared);
  const bool narrowedBV =
      expected.kind() == SourceSort::Kind::BitVector &&
      concrete.sort().kind() == SourceSort::Kind::BitVector &&
      concrete.sort().bitVectorWidth() <= expected.bitVectorWidth();
  if (concrete.sort() != expected && !narrowedBV)
  {
    diagnostic = "certified uninterpreted-function value has the wrong "
                 "SourceSort";
    return false;
  }
  value = concreteValue(manager, concrete, declared);
  return true;
}

bool UFModel::evaluateApplicationInTerm(
    STPMgr* manager, const UFTheoryAdapter* adapter,
    const ASTNode& durableHandle, const std::vector<ASTNode>& actualValues,
    ASTNode& value, std::string& diagnostic)
{
  // An application the solve reached has a certified value; prefer it.
  if (evaluateApplication(manager, adapter, durableHandle, value, diagnostic))
    return true;

  value = ASTNode();
  if (manager == NULL || durableHandle.IsNull() ||
      !durableHandle.IsOwnedBy(manager) ||
      durableHandle.GetKind() != UF_APPLY || durableHandle.Degree() == 0)
  {
    diagnostic = "uninterpreted-function application belongs to another "
                 "context or is invalid";
    return false;
  }
  UFContext* context = manager->getUFContextIfAny();
  const UFDecl* declaration =
      context == NULL ? NULL : context->lookupIdentity(durableHandle[0]);
  if (declaration == NULL)
  {
    diagnostic = "expression is not a registered durable "
                 "uninterpreted-function application";
    return false;
  }
  const UFSignature& signature = declaration->signature();
  if (actualValues.size() != signature.arity())
  {
    diagnostic = "uninterpreted-function application was given the wrong "
                 "number of evaluated actuals";
    return false;
  }

  // The actuals, as the seed keys them -- which is at the lowering sort, and
  // canonicalised.
  //
  // This is the quiet half of the boundary. The checker observed the
  // canonically-packed actual, so a query that supplies a differently
  // payloaded NaN for the same argument is asking about the same value and
  // must reach the same case. Keying the seed with the raw constant instead
  // would fall through to the default, and model evaluation would disagree
  // with the interpretation the define-fun printed -- silently, because both
  // answers are well-sorted.
  UFConcreteTuple arguments;
  arguments.reserve(actualValues.size());
  for (size_t i = 0; i < actualValues.size(); ++i)
  {
    const SourceSort& declared = signature.domain()[i];
    ASTNode actual = actualValues[i];
    if (declared.kind() == SourceSort::Kind::FloatingPoint)
    {
      actual = canonicalConstant(manager, actual, declared);
      if (actual.IsNull())
      {
        diagnostic = "uninterpreted-function application was given a "
                     "floating-point actual that does not fold to a "
                     "canonical value";
        return false;
      }
    }
    UFConcreteValue argument;
    if (!UFConcreteValue::fromConstant(
            actual, UFSignature::loweringSort(declared), argument, diagnostic))
      return false;
    arguments.push_back(argument);
  }

  // The certified seed is a total function: a case per observed tuple, then a
  // default. Nothing certified for this declaration means no application of
  // it was observed, so any constant interpretation is consistent.
  const UFFunctionModelSeedSet* seed =
      (adapter != NULL && adapter->hasCertifiedModel())
          ? adapter->certifiedModelSeed()
          : NULL;
  const UFFunctionModelSeed* function = NULL;
  if (seed != NULL)
  {
    for (const UFFunctionModelSeed& candidate : seed->functions)
      if (candidate.declaration == declaration)
      {
        function = &candidate;
        break;
      }
  }
  if (function == NULL)
  {
    value = concreteValue(
        manager,
        UFConcreteValue::zero(
            UFSignature::loweringSort(signature.codomain())),
        signature.codomain());
    return true;
  }

  for (const UFModelCase& entry : function->cases)
    if (entry.arguments == arguments)
    {
      requireValueSort(entry.result, signature.codomain());
      value = concreteValue(manager, entry.result, signature.codomain());
      return true;
    }

  requireValueSort(function->defaultValue, signature.codomain());
  value = concreteValue(manager, function->defaultValue, signature.codomain());
  return true;
}

bool UFModel::completePublicRoot(STPMgr* manager,
                                 const UFTheoryAdapter& adapter,
                                 ASTNode& completed,
                                 std::string& diagnostic)
{
  completed = ASTNode();
  const LoweredApplicationView* view = adapter.applicationView();
  if (manager == NULL || view == NULL || !view->active() ||
      view->publicRoot.IsNull() || !view->publicRoot.IsOwnedBy(manager))
  {
    diagnostic = "certified UF adapter has no owned active public root";
    return false;
  }
  if (!adapter.hasCertifiedModel())
  {
    diagnostic = "UF public-root completion began before certification";
    return false;
  }

  ASTNodeMap replacements;
  for (const LoweredApplicationRecord& record : view->applications)
  {
    ASTNode constant;
    if (!evaluateApplication(manager, &adapter, record.durableHandle,
                             constant, diagnostic))
      return false;
    if (!replacements.insert(
             std::make_pair(record.durableHandle, constant)).second)
    {
      diagnostic = "UF public-root completion saw a duplicate handle";
      return false;
    }
  }
  ASTNodeMap cache;
  completed = SubstitutionMap::replace(view->publicRoot, replacements, cache,
                                       manager->defaultNodeFactory);
  if (containsKind(completed, UF_APPLY))
  {
    diagnostic = "UF public-root completion left an application behind";
    completed = ASTNode();
    return false;
  }
  return true;
}

bool UFModel::replayPublicRoot(
    AbsRefine_CounterExample& counterexample,
    const UFTheoryAdapter& adapter, std::string& diagnostic)
{
  const LoweredApplicationView* view = adapter.applicationView();
  STPMgr* manager = view == NULL || view->publicRoot.IsNull()
                        ? NULL
                        : view->publicRoot.GetNodeManager();
  ASTNode completed;
  if (!completePublicRoot(manager, adapter, completed, diagnostic))
    return false;
  const ASTNode result = counterexample.QueryFormulaAgainstModel(completed);
  if (result != manager->ASTTrue)
  {
    diagnostic = result == manager->ASTFalse
                     ? "certified UF interpretation does not satisfy the "
                       "preserved public root"
                     : "preserved UF public root did not replay to a Boolean "
                       "constant";
    return false;
  }
  return true;
}

UFFunctionModelSeedSet
UFModel::defaultSeed(const std::vector<const UFDecl*>& declarations)
{
  UFFunctionModelSeedSet seed;
  std::vector<const UFDecl*> ordered = declarations;
  std::sort(ordered.begin(), ordered.end(),
            [](const UFDecl* left, const UFDecl* right) {
              if (left == NULL || right == NULL)
                return left < right;
              return left->id() < right->id();
            });
  for (const UFDecl* declaration : ordered)
  {
    if (declaration == NULL)
      FatalError("UF default model received a null declaration");
    UFFunctionModelSeed function;
    function.declaration = declaration;
    function.defaultValue = UFConcreteValue::zero(
        UFSignature::loweringSort(declaration->signature().codomain()));
    seed.functions.push_back(function);
  }
  return seed;
}

void UFModel::printSMTLIB2(std::ostream& os,
                           const UFFunctionModelSeedSet& seed)
{
  std::vector<const UFFunctionModelSeed*> functions;
  functions.reserve(seed.functions.size());
  for (const UFFunctionModelSeed& function : seed.functions)
    functions.push_back(&function);
  std::sort(functions.begin(), functions.end(), seedFunctionBefore);

  for (const UFFunctionModelSeed* function : functions)
  {
    if (function == NULL || function->declaration == NULL ||
        function->declaration->owner() == NULL)
      FatalError("UF model seed contains an invalid declaration");
    const UFDecl& declaration = *function->declaration;
    const UFSignature& signature = declaration.signature();
    STPMgr* manager = const_cast<STPMgr*>(declaration.owner());
    requireValueSort(function->defaultValue, signature.codomain());

    os << "(define-fun ";
    printQuotedSymbol(os, declaration.name());
    os << " (";
    for (size_t i = 0; i < signature.arity(); ++i)
    {
      if (i != 0)
        os << ' ';
      os << "(x" << i << ' ';
      printSort(os, manager, signature.domain()[i]);
      os << ')';
    }
    os << ") ";
    printSort(os, manager, signature.codomain());
    os << '\n' << "  ";

    // The checker already stores cases in typed tuple order. Emitting them in
    // that order while nesting leaves the lexicographically first case
    // outermost, matching the reference renderer and making text independent
    // of insertion order.
    for (const UFModelCase& modelCase : function->cases)
    {
      if (modelCase.arguments.size() != signature.arity())
        FatalError("UF model seed contains a wrong-arity case");
      requireValueSort(modelCase.result, signature.codomain());
      os << "(ite ";
      printCondition(os, manager, signature, modelCase.arguments);
      os << ' ';
      printValue(os, manager, modelCase.result, signature.codomain());
      os << ' ';
    }
    printValue(os, manager, function->defaultValue, signature.codomain());
    for (size_t i = 0; i < function->cases.size(); ++i)
      os << ')';
    os << ")\n";
  }
}

} // namespace stp

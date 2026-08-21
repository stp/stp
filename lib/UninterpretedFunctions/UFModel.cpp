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
#include "stp/Printer/printers.h"
#include "stp/STPManager/STPManager.h"
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
  (void)manager;
  if (!UFSignature::isSupportedSort(sort))
    FatalError("UF model tried to print an unsupported SourceSort");
  os << sourceSortToSMTLib(sort);
}

// Seed values are stored at the lowering sort; `declared` is the signature
// sort they will be published at. The two differ only for FloatingPoint.
void requireValueSort(const UFConcreteValue& value,
                      const SourceSort& declared)
{
  const SourceSort expected = UFSignature::loweringSort(declared);
  if (value.sort() == expected)
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
  if (value.sort() != expected)
    FatalError("UF concrete-value conversion received a value at the wrong "
               "lowering sort");
  const ASTNode solved = concreteValue(manager, value);
  if (declared.kind() != SourceSort::Kind::FloatingPoint)
    return solved;
  return manager->LiftSourceValue(solved, declared);
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

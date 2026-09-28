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

// A small, installed C++ facade over the stable C uninterpreted-function API.
// It deliberately exposes neither AST internals nor the lowering/checker/SAT
// adapter implementation. Expressions remain ordinary caller-owned C Expr
// handles so this facade interoperates directly with the rest of STP's API.

#ifndef STP_UF_HPP
#define STP_UF_HPP

#include "stp/c_interface.h"

#include <initializer_list>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace stp
{
namespace uf
{

class Context;

class Sort final
{
public:
  enum class Kind
  {
    Bool,
    BitVector,
    FloatingPoint,
    RoundingMode
  };

  static Sort boolean() { return Sort(Kind::Bool, 0, 0); }

  static Sort bitVector(unsigned width)
  {
    if (width == 0)
      throw std::invalid_argument("a bit-vector sort needs a nonzero width");
    return Sort(Kind::BitVector, width, 0);
  }

  // significand counts the hidden bit, as SMT-LIB's (_ FloatingPoint eb sb)
  // does: floatingPoint(8, 24) is an IEEE single and floatingPoint(11, 53) a
  // double. The lower bound is the one vc_fpType enforces, checked here so a
  // bad format is an exception rather than a fatal error.
  static Sort floatingPoint(unsigned exponent, unsigned significand)
  {
    if (exponent < 2 || significand < 2)
      throw std::invalid_argument("a floating-point sort needs at least 2 "
                                  "exponent and 2 significand bits");
    return Sort(Kind::FloatingPoint, exponent, significand);
  }

  static Sort roundingMode() { return Sort(Kind::RoundingMode, 0, 0); }

  Kind kind() const { return kind_; }
  // The bit-vector width; zero for every other sort. A float's format is two
  // numbers and is read with the accessors below rather than through this.
  unsigned width() const { return kind_ == Kind::BitVector ? first_ : 0; }

  unsigned exponentWidth() const
  {
    if (kind_ != Kind::FloatingPoint)
      throw std::invalid_argument("only a floating-point sort has an "
                                  "exponent width");
    return first_;
  }

  unsigned significandWidth() const
  {
    if (kind_ != Kind::FloatingPoint)
      throw std::invalid_argument("only a floating-point sort has a "
                                  "significand width");
    return second_;
  }

private:
  friend class Context;
  Sort(Kind kind, unsigned first, unsigned second)
      : kind_(kind), first_(first), second_(second)
  {
  }

  Type materialize(VC vc) const
  {
    switch (kind_)
    {
      case Kind::Bool:
        return vc_boolType(vc);
      case Kind::FloatingPoint:
        return vc_fpType(vc, static_cast<int>(first_),
                         static_cast<int>(second_));
      case Kind::RoundingMode:
        return vc_fpRoundingModeType(vc);
      case Kind::BitVector:
        break;
    }
    return vc_bvType(vc, static_cast<int>(first_));
  }

  Kind kind_;
  unsigned first_;
  unsigned second_;
};

class Function final
{
public:
  UFDeclHandle raw() const { return declaration_; }
  VC context() const { return vc_; }
  const std::vector<Sort>& domain() const { return domain_; }
  const Sort& codomain() const { return codomain_; }

  // The returned Expr is caller-owned and is released with vc_DeleteExpr.
  Expr applyUninterpretedFunction(const std::vector<Expr>& arguments) const
  {
    if (arguments.size() != domain_.size())
      throw std::invalid_argument("uninterpreted-function arity mismatch");
    Expr result = vc_applyUninterpretedFunction(
        vc_, declaration_, arguments.data(), arguments.size());
    if (result == nullptr)
      throw std::runtime_error("uninterpreted-function application rejected");
    return result;
  }

  Expr operator()(std::initializer_list<Expr> arguments) const
  {
    return applyUninterpretedFunction(std::vector<Expr>(arguments));
  }

private:
  friend class Context;
  Function(VC vc, UFDeclHandle declaration, std::vector<Sort> domain,
           Sort codomain)
      : vc_(vc), declaration_(declaration), domain_(std::move(domain)),
        codomain_(codomain)
  {
  }

  VC vc_;
  UFDeclHandle declaration_;
  std::vector<Sort> domain_;
  Sort codomain_;
};

class Context final
{
public:
  // Context is non-owning. Enabling UF here ensures handles subsequently
  // built through the C API participate in its bounded live-handle registry.
  explicit Context(VC vc) : vc_(vc)
  {
    if (vc_ == nullptr)
      throw std::invalid_argument("an uninterpreted-function context needs a VC");
    vc_setFlag(vc_, 'u');
  }

  VC raw() const { return vc_; }

  Function declareUninterpretedFunction(const std::string& name,
                                         std::vector<Sort> domain,
                                         Sort codomain) const
  {
    if (domain.empty())
      throw std::invalid_argument("zero-arity functions are ordinary symbols");

    std::vector<Type> domainTypes;
    domainTypes.reserve(domain.size());
    Type codomainType = nullptr;
    try
    {
      for (const Sort& sort : domain)
        domainTypes.push_back(sort.materialize(vc_));
      codomainType = codomain.materialize(vc_);
      const UFDeclHandle declaration = vc_declareUninterpretedFunction(
          vc_, name.c_str(), domainTypes.data(), domainTypes.size(),
          codomainType);
      for (Type type : domainTypes)
        vc_DeleteExpr(type);
      domainTypes.clear();
      vc_DeleteExpr(codomainType);
      codomainType = nullptr;
      if (declaration == 0)
        throw std::runtime_error(
            "uninterpreted-function declaration rejected");
      return Function(vc_, declaration, std::move(domain), codomain);
    }
    catch (...)
    {
      for (Type type : domainTypes)
        vc_DeleteExpr(type);
      vc_DeleteExpr(codomainType);
      throw;
    }
  }

  // The returned Expr is caller-owned and is released with vc_DeleteExpr.
  Expr getUninterpretedFunctionValue(Expr application) const
  {
    Expr value = vc_getUninterpretedFunctionValue(vc_, application);
    if (value == nullptr)
      throw std::runtime_error(
          "uninterpreted-function value is not available");
    return value;
  }

private:
  VC vc_;
};

} // namespace uf
} // namespace stp

#endif

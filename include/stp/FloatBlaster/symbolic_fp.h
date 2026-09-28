/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: January 2021
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

// STP's backend for symfpu: the value classes symfpu computes with
// (propositions, signed/unsigned bitvectors, rounding modes) implemented as
// thin wrappers over ASTNode, building circuits through the manager's node
// factory. blast_* lower one floating-point operation each; FloatBlaster
// dispatches to them.

#ifndef SYMBOLIC_FP_H
#define SYMBOLIC_FP_H

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/STPManager/STPManager.h"

#include <cassert>
#include <type_traits>

// symfpu states its preconditions, postconditions and invariants through
// three macros, and calls them with arguments of two quite different kinds:
// a plain `bool` -- a width, a position, a flag it can settle while building
// the circuit -- or a `prop`. For this back end a `prop` is not a value. It
// is a circuit constructor: PRECONDITION(uf.valid(format)) builds a
// wellFormed conjunction, a getSubnormalAmount, an orderEncode and a mask
// test, every node of it through the manager's simplifying factory.
//
// symfpu's default expansion is an ordinary function call, `t::precondition(X)`,
// so the argument is fully evaluated before the overload that receives it can
// decide what to do with it -- and the `prop` overload can only throw it away,
// since a symbolic property cannot be checked while the circuit is being
// built. valid() and wellFormed() are reached from nowhere else in symfpu, so
// every node those arguments construct is dead on arrival, in every build
// configuration: the overload is empty with and without NDEBUG.
//
// properties.h guards all three macros with #ifndef precisely so that a back
// end can say otherwise. Say otherwise. `decltype` does not evaluate its
// operand, so asking the type first costs nothing and lets the `bool`
// properties -- which are real checks, and cheap -- go on being asserted while
// the `prop` ones are never built at all.
//
// Both branches still have to compile, which is what keeps this honest: it
// stays a question about the argument's type, not a blanket suppression, so a
// symfpu update that changed a property's shape would not slip through.
//
// This must come before any symfpu header, which is why every translation unit
// that uses symfpu includes *this* header first. Enforced rather than trusted:
// getting the order wrong would not fail, it would silently restore the
// expansion that builds and discards the circuits, and nothing downstream
// would look any different.
#ifdef SYMFPU_PROPERTIES
#error "stp/FloatBlaster/symbolic_fp.h must be included before any symfpu \
header, so that it defines PRECONDITION/POSTCONDITION/INVARIANT before \
symfpu/utils/properties.h supplies its own."
#endif

namespace stp
{
namespace symbolic_fp
{

// The two halves of the decision above. The `bool` overload is the check
// symfpu wanted; the template one exists so that the branch the macro
// discards is still *well-formed* for a `prop`, which outside a template it
// has to be -- `if constexpr` only skips instantiating a discarded branch
// inside one, and every symfpu use of these macros happens to be in a
// template. Without the overload this compiles there and nowhere else.
inline void assertProperty(const bool holds)
{
  assert(holds);
  (void)holds;
}

template <class T> inline void assertProperty(const T&) {}

} // namespace symbolic_fp
} // namespace stp

#define STP_SYMFPU_PROPERTY(X)                                                 \
  do                                                                           \
  {                                                                            \
    if constexpr (std::is_same_v<std::decay_t<decltype(X)>, bool>)             \
      ::stp::symbolic_fp::assertProperty(X);                                   \
  } while (false)

#define PRECONDITION(X) STP_SYMFPU_PROPERTY(X)
#define POSTCONDITION(X) STP_SYMFPU_PROPERTY(X)
#define INVARIANT(X) STP_SYMFPU_PROPERTY(X)

#include "symfpu/core/unpackedFloat.h"

namespace stp
{
namespace symbolic_fp
{

typedef uint32_t bitWidthType;
class roundingMode;
class floatingPointTypeInfo;
class proposition;
template <bool T> class bitVector;

class traits
{
public:
  typedef bitWidthType bwt;
  typedef roundingMode rm;
  typedef floatingPointTypeInfo fpt;
  typedef proposition prop;
  typedef bitVector<true> sbv;
  typedef bitVector<false> ubv;

  static roundingMode RNE(void);
  static roundingMode RNA(void);
  static roundingMode RTP(void);
  static roundingMode RTN(void);
  static roundingMode RTZ(void);

  static void precondition(const bool b);
  static void postcondition(const bool b);
  static void invariant(const bool b);
  static void precondition(const prop& p);
  static void postcondition(const prop& p);
  static void invariant(const prop& p);
};

typedef traits::bwt bwt;
typedef symfpu::unpackedFloat<traits> uf;

class nodeWrapper : public ASTNode
{
protected:
  nodeWrapper(const ASTNode& n);
};

class proposition : public nodeWrapper
{
protected:
  bool checkNodeType(const ASTNode& node);

  friend ::symfpu::ite<proposition, proposition>;

public:
  proposition(const ASTNode n);
  proposition(bool v);
  proposition(const proposition& old);

  proposition operator!(void) const;
  proposition operator&&(const proposition& op) const;
  proposition operator||(const proposition& op) const;
  proposition operator==(const proposition& op) const;
  proposition operator^(const proposition& op) const;
};

// A rounding mode needs no valid() here: a symbolic mode can only enter via
// a declared RoundingMode symbol, and the declaration itself asserts the
// one-hot validity constraint (Cpp_interface::addRoundingModeSymbol).
class roundingMode : public nodeWrapper
{
protected:
  friend ::symfpu::ite<proposition, roundingMode>;

public:
  roundingMode(const ASTNode n);
  roundingMode(const unsigned v);
  roundingMode(const roundingMode& old);

  proposition operator==(const roundingMode& op) const;
};

template <bool T> struct signedToLiteralType;

template <> struct signedToLiteralType<true>
{
  typedef int literalType;
};

template <> struct signedToLiteralType<false>
{
  typedef unsigned int literalType;
};

template <bool isSigned> class bitVector : public nodeWrapper
{
protected:
  typedef typename signedToLiteralType<isSigned>::literalType literalType;

  ASTNode fromProposition(const ASTNode& node) const;
  bool checkNodeType(const ASTNode& n);
  friend bitVector<!isSigned>;

  friend ::symfpu::ite<proposition, bitVector<isSigned>>;

public:
  bitVector(const ASTNode n);
  bitVector(const bwt w, const unsigned v);
  bitVector(const proposition& p);
  bitVector(const bitVector<isSigned>& old);

  bwt getWidth(void) const;

  static bitVector<isSigned> one(const bwt& w);
  static bitVector<isSigned> zero(const bwt& w);
  static bitVector<isSigned> allOnes(const bwt& w);

  proposition isAllOnes() const;
  proposition isAllZeros() const;

  static bitVector<isSigned> maxValue(const bwt& w);
  static bitVector<isSigned> minValue(const bwt& w);

  bitVector<isSigned> operator<<(const bitVector<isSigned>& op) const;
  bitVector<isSigned> operator>>(const bitVector<isSigned>& op) const;
  bitVector<isSigned> operator|(const bitVector<isSigned>& op) const;
  bitVector<isSigned> operator&(const bitVector<isSigned>& op) const;
  bitVector<isSigned> operator+(const bitVector<isSigned>& op) const;
  bitVector<isSigned> operator-(const bitVector<isSigned>& op) const;
  bitVector<isSigned> operator*(const bitVector<isSigned>& op) const;
  bitVector<isSigned> operator/(const bitVector<isSigned>& op) const;
  bitVector<isSigned> operator%(const bitVector<isSigned>& op) const;
  bitVector<isSigned> operator-(void) const;
  bitVector<isSigned> operator~(void) const;
  bitVector<isSigned> increment() const;
  bitVector<isSigned> decrement() const;
  bitVector<isSigned> signExtendRightShift(const bitVector<isSigned>& op) const;

  bitVector<isSigned> modularLeftShift(const bitVector<isSigned>& op) const;
  bitVector<isSigned> modularRightShift(const bitVector<isSigned>& op) const;
  bitVector<isSigned> modularIncrement() const;
  bitVector<isSigned> modularDecrement() const;
  bitVector<isSigned> modularAdd(const bitVector<isSigned>& op) const;
  bitVector<isSigned> modularSubtract(const bitVector<isSigned>& op) const;
  bitVector<isSigned> modularNegate() const;

  proposition operator==(const bitVector<isSigned>& op) const;
  proposition operator<=(const bitVector<isSigned>& op) const;
  proposition operator>=(const bitVector<isSigned>& op) const;
  proposition operator<(const bitVector<isSigned>& op) const;
  proposition operator>(const bitVector<isSigned>& op) const;

  bitVector<true> toSigned(void) const;
  bitVector<false> toUnsigned(void) const;

  bitVector<isSigned> extend(bwt extension) const;
  bitVector<isSigned> contract(bwt reduction) const;
  bitVector<isSigned> resize(bwt newSize) const;
  bitVector<isSigned> matchWidth(const bitVector<isSigned>& op) const;
  bitVector<isSigned> append(const bitVector<isSigned>& op) const;

  bitVector<isSigned> extract(bwt upper, bwt lower) const;
};

class floatingPointTypeInfo
{
public:
  floatingPointTypeInfo(unsigned exp, unsigned sig);
  floatingPointTypeInfo(const floatingPointTypeInfo& old);

  bitWidthType exponentWidth(void) const;
  bitWidthType significandWidth(void) const;

  bitWidthType packedWidth(void) const;
  bitWidthType packedExponentWidth(void) const;
  bitWidthType packedSignificandWidth(void) const;

private:
  bitWidthType m_exp;
  bitWidthType m_sig;
};

// Point the backend at the manager whose nodes are being blasted. symfpu
// constructs backend values through static trait calls (traits::RNE() takes
// no context), so the manager and factory have to live in file statics;
// this repoints them, and is called before every top-level blast.
void init(STPMgr* bm);

// Operations over SymFPU's unpacked representation.  FloatBlast uses these
// to keep a floating-point DAG unpacked across consecutive operations and
// materialise packed IEEE bits only at a real carrier boundary.  The packed
// blast_* facade below remains for callers that lower one operation at a
// time (notably the constant evaluator).
namespace unpacked
{
uf decode(const floatingPointTypeInfo& size, const ASTNode& packed);
ASTNode encode(const floatingPointTypeInfo& size, const uf& value);

// A floating-point-valued source ITE is an ITE over every component of the
// unpacked representation.  `condition` is a Boolean ASTNode.
uf select(const ASTNode& condition, const uf& when_true,
          const uf& when_false);

ASTNode smtEqual(const floatingPointTypeInfo& size, const uf& lhs,
                 const uf& rhs);

uf add(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& lhs,
       const uf& rhs);
uf sub(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& lhs,
       const uf& rhs);
uf mul(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& lhs,
       const uf& rhs);
uf div(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& lhs,
       const uf& rhs);
uf fma(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& x,
       const uf& y, const uf& z);
uf sqrt(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& value);
uf rem(const floatingPointTypeInfo& size, const uf& lhs, const uf& rhs);
uf min(const floatingPointTypeInfo& size, const uf& lhs, const uf& rhs,
       const ASTNode& zero_case);
uf max(const floatingPointTypeInfo& size, const uf& lhs, const uf& rhs,
       const ASTNode& zero_case);
uf abs(const floatingPointTypeInfo& size, const uf& value);
uf neg(const floatingPointTypeInfo& size, const uf& value);
uf roundToIntegral(const floatingPointTypeInfo& size, const ASTNode& rm,
                   const uf& value);

// Floating-point consumers whose result is already in the target language.
ASTNode toBV(const floatingPointTypeInfo& size, const ASTNode& rm,
             const uf& value, bitWidthType target_width,
             const ASTNode& undef, bool is_signed);
ASTNode ieeeEqual(const floatingPointTypeInfo& size, const uf& lhs,
                  const uf& rhs);
ASTNode lessThan(const floatingPointTypeInfo& size, const uf& lhs,
                 const uf& rhs);
ASTNode lessThanOrEqual(const floatingPointTypeInfo& size, const uf& lhs,
                        const uf& rhs);
// Whether adding two already-rounded values of `size` can produce either
// signed zero.  This deliberately consumes the operands rather than an
// unpacked addition result, so callers that observe only zero magnitude do
// not have to construct the complete rounded sum.
ASTNode addIsZero(const floatingPointTypeInfo& size, const uf& lhs,
                  const uf& rhs);
ASTNode isNormal(const floatingPointTypeInfo& size, const uf& value);
ASTNode isSubnormal(const floatingPointTypeInfo& size, const uf& value);
ASTNode isZero(const floatingPointTypeInfo& size, const uf& value);
ASTNode isInfinite(const floatingPointTypeInfo& size, const uf& value);
ASTNode isNaN(const floatingPointTypeInfo& size, const uf& value);
ASTNode isNegative(const floatingPointTypeInfo& size, const uf& value);
ASTNode isPositive(const floatingPointTypeInfo& size, const uf& value);

uf convertBVToFloat(const floatingPointTypeInfo& target, const ASTNode& rm,
                    const ASTNode& bits, bool is_signed);
uf convertFloatToFloat(const floatingPointTypeInfo& source,
                       const floatingPointTypeInfo& target,
                       const ASTNode& rm, const uf& value);
} // namespace unpacked

} // namespace symbolic_fp

} // namespace stp

#endif

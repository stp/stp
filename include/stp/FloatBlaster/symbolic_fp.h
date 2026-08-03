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

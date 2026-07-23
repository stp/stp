/********************************************************************
 * AUTHORS: Andrew V. Jones
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

#ifndef SYMBOLIC_FP_H
#define SYMBOLIC_FP_H

#define STP_USE_SYMFPU

#include "stp/AST/AST.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"

#ifdef STP_USE_SYMFPU
#include "symfpu/core/unpackedFloat.h"
#endif

namespace stp
{

typedef ASTNode Node;
typedef ASTNode TNode;
typedef ASTNode TypeNode;
typedef ASTNode FloatingPointSize;

namespace symbolic_fp
{

enum rounding_modes
{
  ROUND_NEAREST_TIES_TO_EVEN = 1,
  ROUND_TOWARD_POSITIVE = ROUND_NEAREST_TIES_TO_EVEN << 1,
  ROUND_TOWARD_NEGATIVE = ROUND_TOWARD_POSITIVE << 1,
  ROUND_TOWARD_ZERO = ROUND_TOWARD_NEGATIVE << 1,
  ROUND_NEAREST_TIES_TO_AWAY = ROUND_TOWARD_ZERO << 1,
};

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

class nodeWrapper : public Node
{
protected:
  nodeWrapper(const Node& n);
};

class proposition : public nodeWrapper
{
protected:
  bool checkNodeType(const TNode node);

#ifdef STP_USE_SYMFPU
  friend ::symfpu::ite<proposition, proposition>;
#endif

public:
  proposition(const Node n);
  proposition(bool v);
  proposition(const proposition& old);

  proposition operator!(void) const;
  proposition operator&&(const proposition& op) const;
  proposition operator||(const proposition& op) const;
  proposition operator==(const proposition& op) const;
  proposition operator^(const proposition& op) const;
};

class roundingMode : public nodeWrapper
{
protected:
  bool checkNodeType(const TNode n);

#ifdef STP_USE_SYMFPU
  friend ::symfpu::ite<proposition, roundingMode>;
#endif

public:
  roundingMode(const Node n);
  roundingMode(const unsigned v);
  roundingMode(const roundingMode& old);

  proposition valid(void) const;
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

  Node boolNodeToBV(Node node) const;
  Node BVToBoolNode(Node node) const;

  Node fromProposition(Node node) const;
  Node toProposition(Node node) const;
  bool checkNodeType(const TNode n);
  friend bitVector<!isSigned>;

#ifdef STP_USE_SYMFPU
  friend ::symfpu::ite<proposition, bitVector<isSigned>>;
#endif

public:
  bitVector(const Node n);
  bitVector(const bwt w, const unsigned v);
  bitVector(const proposition& p);
  bitVector(const bitVector<isSigned>& old);
#if 0
    bitVector(const BitVector &old);
#endif

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

  TypeNode getTypeNode(void) const;

  bitWidthType exponentWidth(void) const;
  bitWidthType significandWidth(void) const;

  bitWidthType packedWidth(void) const;
  bitWidthType packedExponentWidth(void) const;
  bitWidthType packedSignificandWidth(void) const;

private:
  bitWidthType m_exp;
  bitWidthType m_sig;
};

void init_vc(STPMgr* _bm);

ASTNode blast_smt_eq(const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpadd(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpsub(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpmul(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpdiv(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_pos_inf(const ASTNode& orig);
ASTNode blast_neg_inf(const ASTNode& orig);
ASTNode blast_nan(const ASTNode& orig);
ASTNode blast_zero(const ASTNode& orig, bool sign);
ASTNode round_trip(const ASTNode& expr, ASTNode** side);
ASTNode blast_round_to_integral(const ASTNode& rm, const ASTNode& expr);

ASTNode blast_fpfma(const ASTNode& rm, const ASTNode& x, const ASTNode& y,
                    const ASTNode& z);
ASTNode blast_fpsqrt(const ASTNode& rm, const ASTNode& expr);
ASTNode blast_fprem(const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpmin(const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpmax(const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpabs(const ASTNode& expr);
ASTNode blast_fpneg(const ASTNode& expr);

// Ordering predicates. These return Boolean-typed nodes, not floats.
ASTNode blast_fplt(const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpleq(const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpeq(const ASTNode& lhs, const ASTNode& rhs);

// Classification predicates, also Boolean-typed.
ASTNode blast_is_normal(const ASTNode& expr);
ASTNode blast_is_subnormal(const ASTNode& expr);
ASTNode blast_is_zero(const ASTNode& expr);
ASTNode blast_is_infinite(const ASTNode& expr);
ASTNode blast_is_nan(const ASTNode& expr);
ASTNode blast_is_negative(const ASTNode& expr);
ASTNode blast_is_positive(const ASTNode& expr);

// ((_ to_fp e s) bv) -- reinterpret a bitvector's bits as a float.
ASTNode blast_reinterpret(const ASTNode& bits, bitWidthType exp_width,
                          bitWidthType sig_width);

// ((_ to_fp e s) rm f) -- reformat an existing float under a rounding mode.
ASTNode blast_convert_float_to_float(const ASTNode& rm, const ASTNode& expr,
                                     bitWidthType target_exp,
                                     bitWidthType target_sig);

} // namespace symbolic_fp

} // namespace stp

#endif

// EOF

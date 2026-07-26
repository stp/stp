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

ASTNode blast_smt_eq(const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpadd(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpsub(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpmul(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_fpdiv(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs);
ASTNode blast_round_to_integral(const ASTNode& rm, const ASTNode& expr);

ASTNode blast_fpfma(const ASTNode& rm, const ASTNode& x, const ASTNode& y,
                    const ASTNode& z);
ASTNode blast_fpsqrt(const ASTNode& rm, const ASTNode& expr);
ASTNode blast_fprem(const ASTNode& lhs, const ASTNode& rhs);
// zero_case says which zero fp.min/fp.max return given +0 and -0, where
// SMT-LIB leaves the answer open. FpTotalise supplies it.
ASTNode blast_fpmin(const ASTNode& lhs, const ASTNode& rhs,
                    const ASTNode& zero_case);
ASTNode blast_fpmax(const ASTNode& lhs, const ASTNode& rhs,
                    const ASTNode& zero_case);
// fp.to_ubv/fp.to_sbv. `undef` supplies the result for the inputs where
// SMT-LIB leaves it unspecified: NaN, the infinities, and anything out of
// range for the target width.
ASTNode blast_fp_to_bv(const ASTNode& rm, const ASTNode& expr,
                       bitWidthType target_width, const ASTNode& undef,
                       bool is_signed);

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

// ((_ to_fp e s) rm bv) / ((_ to_fp_unsigned e s) rm bv) -- convert an
// integer held in a bitvector to the nearest float under a rounding mode.
ASTNode blast_convert_bv_to_float(const ASTNode& rm, const ASTNode& bits,
                                  bitWidthType exp_width,
                                  bitWidthType sig_width, bool is_signed);

// ((_ to_fp e s) rm f) -- reformat an existing float under a rounding mode.
ASTNode blast_convert_float_to_float(const ASTNode& rm, const ASTNode& expr,
                                     bitWidthType target_exp,
                                     bitWidthType target_sig);

} // namespace symbolic_fp

} // namespace stp

#endif

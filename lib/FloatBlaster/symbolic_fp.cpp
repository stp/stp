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

#include "stp/FloatBlaster/symbolic_fp.h"

#include "stp/NodeFactory/NodeFactory.h"
#include "stp/STPManager/STPManager.h"

#include <cassert>

#include "symfpu/core/add.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/core/unpackedFloat.h"
#include "symfpu/utils/numberOfRoundingModes.h"

using namespace stp;
using namespace stp::symbolic_fp;

// The manager and factory the circuits are built into. symfpu constructs
// backend values through static trait calls (traits::RNE() and friends take
// no context), so the context has to live in file statics; init() repoints
// them before every top-level blast (see FloatBlast::topLevel).
// Each thread needs its own pair: independent validity checkers may blast in
// parallel, and a process-global pair would make one thread build through the
// other thread's manager and concurrently mutate its hash-cons tables.
// The factory is the manager's default (simplifying) factory: constant
// operands fold as the circuit is built, which is what lets the constant
// evaluator blast-fold floating-point operations on constants.
static THREAD_LOCAL_IE STPMgr* s_bm = nullptr;
static THREAD_LOCAL_IE NodeFactory* s_nf = nullptr;

namespace stp
{
namespace symbolic_fp
{
void init(STPMgr* bm)
{
  assert(bm != nullptr);
  s_bm = bm;
  s_nf = bm->defaultNodeFactory;
}
} // namespace symbolic_fp
} // namespace stp

nodeWrapper::nodeWrapper(const ASTNode& n) : ASTNode(n) {}

/****************************************************************
 * roundingMode                                                 *
 ****************************************************************/

roundingMode::roundingMode(unsigned int v)
    : nodeWrapper(s_bm->CreateBVConst(SYMFPU_NUMBER_OF_ROUNDING_MODES, v))
{
}

roundingMode::roundingMode(const ASTNode n) : nodeWrapper(n) {}

roundingMode::roundingMode(const roundingMode& old) : nodeWrapper(old) {}

proposition roundingMode::operator==(const roundingMode& op) const
{
  return proposition(s_nf->CreateNode(EQ, *this, op));
}

roundingMode traits::RNE(void)
{
  return roundingMode(ROUND_NEAREST_TIES_TO_EVEN);
}

roundingMode traits::RNA(void)
{
  return roundingMode(ROUND_NEAREST_TIES_TO_AWAY);
}

roundingMode traits::RTP(void)
{
  return roundingMode(ROUND_TOWARD_POSITIVE);
}

roundingMode traits::RTN(void)
{
  return roundingMode(ROUND_TOWARD_NEGATIVE);
}

roundingMode traits::RTZ(void)
{
  return roundingMode(ROUND_TOWARD_ZERO);
}

void traits::precondition(const bool b)
{
  assert(b);
  (void)b;
}

void traits::postcondition(const bool b)
{
  assert(b);
  (void)b;
}

void traits::invariant(const bool b)
{
  assert(b);
  (void)b;
}

// Symbolic properties cannot be checked at blast time.
void traits::precondition(const prop&) {}

void traits::postcondition(const prop&) {}

void traits::invariant(const prop&) {}

/****************************************************************
 * proposition                                                  *
 ****************************************************************/

proposition::proposition(const ASTNode n) : nodeWrapper(n)
{
  assert(checkNodeType(*this));
}

proposition::proposition(bool v)
    : nodeWrapper(v ? s_bm->ASTTrue : s_bm->ASTFalse)
{
  assert(checkNodeType(*this));
}

proposition::proposition(const proposition& old) : nodeWrapper(old)
{
  assert(checkNodeType(*this));
}

bool proposition::checkNodeType(const ASTNode& node)
{
  return node.GetType() == stp::BOOLEAN_TYPE;
}

proposition proposition::operator!(void) const
{
  return proposition(s_nf->CreateNode(NOT, *this));
}

proposition proposition::operator&&(const proposition& op) const
{
  return proposition(s_nf->CreateNode(AND, *this, op));
}

proposition proposition::operator||(const proposition& op) const
{
  return proposition(s_nf->CreateNode(OR, *this, op));
}

proposition proposition::operator==(const proposition& op) const
{
  return proposition(s_nf->CreateNode(IFF, *this, op));
}

proposition proposition::operator^(const proposition& op) const
{
  return proposition(s_nf->CreateNode(XOR, *this, op));
}

/****************************************************************
 * bitVector                                                    *
 ****************************************************************/

template <bool isSigned>
bitVector<isSigned>::bitVector(const ASTNode n) : nodeWrapper(n)
{
  assert(checkNodeType(*this));
}

template <bool isSigned>
bool bitVector<isSigned>::checkNodeType(const ASTNode& n)
{
  // Floats are carried packed, so a float-typed node is bits too.
  return (n.GetType() == stp::BITVECTOR_TYPE ||
          n.GetType() == stp::FLOATINGPOINT_TYPE) &&
         n.GetValueWidth() > 0;
}

template <bool isSigned>
bitVector<isSigned>::bitVector(const bitWidthType w, const unsigned v)
    : nodeWrapper(s_bm->CreateBVConst(w, v))
{
  assert(checkNodeType(*this));
}

template <bool isSigned>
bitVector<isSigned>::bitVector(const proposition& p)
    : nodeWrapper(fromProposition(p))
{
}

template <bool isSigned>
bitVector<isSigned>::bitVector(const bitVector<isSigned>& old)
    : nodeWrapper(old)
{
  assert(checkNodeType(*this));
}

// symfpu's propositions are Boolean nodes; where it stores one into a
// bitvector, select a bit.
template <bool isSigned>
ASTNode bitVector<isSigned>::fromProposition(const ASTNode& node) const
{
  // Sequenced deliberately: two constants built in one call expression are
  // unordered against each other, and their node ids decide how commutative
  // children later sort. See the note in FpTotalise::signSelect.
  const ASTNode one = s_bm->CreateOneConst(1);
  const ASTNode zero = s_bm->CreateZeroConst(1);
  return s_nf->CreateTerm(ITE, 1, node, one, zero);
}

template <bool isSigned> bitWidthType bitVector<isSigned>::getWidth(void) const
{
  const bitWidthType ret = GetValueWidth();
  assert(ret > 0);
  return ret;
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::one(const bitWidthType& w)
{
  return bitVector<isSigned>(w, 1);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::zero(const bitWidthType& w)
{
  return bitVector<isSigned>(w, 0);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::allOnes(const bitWidthType& w)
{
  return bitVector<isSigned>(~zero(w));
}

template <bool isSigned> proposition bitVector<isSigned>::isAllOnes() const
{
  return (*this == bitVector<isSigned>::allOnes(this->getWidth()));
}

template <bool isSigned> proposition bitVector<isSigned>::isAllZeros() const
{
  return (*this == bitVector<isSigned>::zero(this->getWidth()));
}

template <> bitVector<true> bitVector<true>::maxValue(const bitWidthType& w)
{
  // A clear sign bit followed by ones.
  bitVector<true> leadingZero(bitVector<true>::zero(1));
  bitVector<true> base(bitVector<true>::allOnes(w - 1));
  return bitVector<true>(s_nf->CreateTerm(BVCONCAT, w, leadingZero, base));
}

template <> bitVector<false> bitVector<false>::maxValue(const bitWidthType& w)
{
  return bitVector<false>::allOnes(w);
}

template <> bitVector<true> bitVector<true>::minValue(const bitWidthType& w)
{
  // The most negative two's-complement value is a set sign bit followed by
  // zeros. This used to build a *clear* sign bit followed by zeros, which is
  // simply 0 -- so the signed minimum compared equal to zero.
  bitVector<true> leadingOne(bitVector<true>::one(1));
  bitVector<true> base(bitVector<true>::zero(w - 1));
  return bitVector<true>(s_nf->CreateTerm(BVCONCAT, w, leadingOne, base));
}

template <> bitVector<false> bitVector<false>::minValue(const bitWidthType& w)
{
  return bitVector<false>::zero(w);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator<<(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(
      s_nf->CreateTerm(BVLEFTSHIFT, getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator>>(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(s_nf->CreateTerm(
      isSigned ? BVSRSHIFT : BVRIGHTSHIFT, getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator|(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(s_nf->CreateTerm(BVOR, getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator&(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(s_nf->CreateTerm(BVAND, getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator+(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(s_nf->CreateTerm(BVPLUS, getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator-(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(s_nf->CreateTerm(BVSUB, getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator*(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(s_nf->CreateTerm(BVMULT, getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator/(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(
      s_nf->CreateTerm(isSigned ? SBVDIV : BVDIV, getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator%(const bitVector<isSigned>& op) const
{
  // SymFPU's other symbolic backends map signed % to signed remainder (the
  // quotient truncates toward zero, and the result follows the dividend's
  // sign). SMT-LIB bvsmod follows the divisor's sign instead.
  return bitVector<isSigned>(
      s_nf->CreateTerm(isSigned ? SBVREM : BVMOD, getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::operator-(void) const
{
  return bitVector<isSigned>(s_nf->CreateTerm(BVUMINUS, getWidth(), *this));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::operator~(void) const
{
  return bitVector<isSigned>(s_nf->CreateTerm(BVNOT, getWidth(), *this));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::increment() const
{
  return *this + one(getWidth());
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::decrement() const
{
  return *this - one(getWidth());
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::signExtendRightShift(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(
      s_nf->CreateTerm(BVSRSHIFT, getWidth(), *this, op));
}

// symfpu distinguishes the modular operations (that may wrap) from the
// plain ones (guarded by preconditions); on bitvectors they coincide.
template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::modularLeftShift(const bitVector<isSigned>& op) const
{
  return *this << op;
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::modularRightShift(const bitVector<isSigned>& op) const
{
  return *this >> op;
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::modularIncrement() const
{
  return this->increment();
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::modularDecrement() const
{
  return this->decrement();
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::modularAdd(const bitVector<isSigned>& op) const
{
  return *this + op;
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::modularSubtract(const bitVector<isSigned>& op) const
{
  return *this - op;
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::modularNegate() const
{
  return -(*this);
}

template <bool isSigned>
proposition bitVector<isSigned>::operator==(const bitVector<isSigned>& op) const
{
  // As with the orderings below: symfpu compares values, so a narrower
  // operand is brought up to width rather than mis-typing the EQ. (symfpu
  // only calls == width-matched today; <= and >= are built from < and ==,
  // and would hand a width-mismatched pair straight through.)
  if (getWidth() < op.getWidth())
    return proposition(s_nf->CreateNode(EQ, matchWidth(op), op));
  if (op.getWidth() < getWidth())
    return proposition(s_nf->CreateNode(EQ, *this, op.matchWidth(*this)));
  return proposition(s_nf->CreateNode(EQ, *this, op));
}

template <bool isSigned>
proposition bitVector<isSigned>::operator<(const bitVector<isSigned>& op) const
{
  // symfpu compares values of different widths in a few places; bring the
  // narrower operand up first.
  const Kind k = isSigned ? BVSLT : BVLT;
  if (getWidth() < op.getWidth())
    return proposition(s_nf->CreateNode(k, matchWidth(op), op));
  if (op.getWidth() < getWidth())
    return proposition(s_nf->CreateNode(k, *this, op.matchWidth(*this)));
  return proposition(s_nf->CreateNode(k, *this, op));
}

template <bool isSigned>
proposition bitVector<isSigned>::operator<=(const bitVector<isSigned>& op) const
{
  return (*this < op) || (*this == op);
}

template <bool isSigned>
proposition bitVector<isSigned>::operator>=(const bitVector<isSigned>& op) const
{
  return (*this > op) || (*this == op);
}

template <bool isSigned>
proposition bitVector<isSigned>::operator>(const bitVector<isSigned>& op) const
{
  return proposition(
      s_nf->CreateNode(isSigned ? BVSLT : BVLT, op, *this));
}

template <bool isSigned>
bitVector<true> bitVector<isSigned>::toSigned(void) const
{
  return bitVector<true>(*this);
}

template <bool isSigned>
bitVector<false> bitVector<isSigned>::toUnsigned(void) const
{
  return bitVector<false>(*this);
}

template <>
bitVector<true> bitVector<true>::extend(bitWidthType extension) const
{
  if (extension == 0)
    return *this;

  const bitWidthType new_length = getWidth() + extension;
  return bitVector<true>(
      s_nf->CreateTerm(BVSX, new_length, *this,
                       s_bm->CreateBVConst(32, new_length)));
}

template <>
bitVector<false> bitVector<false>::extend(bitWidthType extension) const
{
  // Extending by nothing is the identity. Falling through would ask for a
  // zero-width constant to concatenate, which STP rejects. symfpu's
  // conversion path does call this with an extension of zero.
  if (extension == 0)
    return *this;

  const bitWidthType new_length = getWidth() + extension;
  return bitVector<false>(
      s_nf->CreateTerm(BVCONCAT, new_length,
                       s_bm->CreateZeroConst(extension), *this));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::contract(bitWidthType reduction) const
{
  // Fail closed for the same reason as matchWidth: the subtraction below is
  // unsigned, so an over-large reduction underflows into an extract of an
  // absurd range rather than stopping.
  if (this->getWidth() <= reduction)
  {
    FatalError("symbolic_fp: contract would remove every bit of a bitvector; "
               "symfpu asked to narrow a value past its own width");
  }
  return extract((this->getWidth() - 1) - reduction, 0);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::resize(bitWidthType newSize) const
{
  const bitWidthType width = this->getWidth();

  if (newSize > width)
    return this->extend(newSize - width);
  if (newSize < width)
    return this->contract(width - newSize);
  return *this;
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::matchWidth(const bitVector<isSigned>& op) const
{
  // Fail closed rather than assert. bitWidthType is unsigned, so a violated
  // precondition does not merely widen the wrong way -- the subtraction wraps
  // to about 2^32, extend asks for a constant of that width, and the circuit
  // builder walks off the end of a bitvector. An assert would catch it, but
  // CMAKE_BUILD_TYPE=Release compiles asserts out (CMakeLists.txt forces
  // ENABLE_ASSERTIONS off there), so the builds users ship are exactly the
  // ones that would segfault. The formats that used to reach here are fixed
  // in patches/symfpu/ rather than refused at the front door, so nothing is
  // expected to trip this; it stays as the backstop that turns a future
  // width miscalculation into a diagnosis instead of a crash.
  if (this->getWidth() > op.getWidth())
  {
    FatalError("symbolic_fp: matchWidth cannot narrow a bitvector; symfpu "
               "asked to resize a value wider than its target, which is a "
               "width miscalculation in the floating-point lowering");
  }
  if (this->getWidth() == op.getWidth())
    return *this;
  return this->extend(op.getWidth() - this->getWidth());
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::append(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(s_nf->CreateTerm(
      BVCONCAT, getWidth() + op.getWidth(), *this, op));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::extract(bitWidthType upper,
                                                 bitWidthType lower) const
{
  assert(upper >= lower);
  // Sequenced deliberately; see the note in fromProposition.
  const ASTNode hi = s_bm->CreateBVConst(32, upper);
  const ASTNode lo = s_bm->CreateBVConst(32, lower);
  return bitVector<isSigned>(
      s_nf->CreateTerm(BVEXTRACT, (upper - lower) + 1, *this, hi, lo));
}

/****************************************************************
 * floatingPointTypeInfo                                        *
 ****************************************************************/

floatingPointTypeInfo::floatingPointTypeInfo(unsigned exp, unsigned sig)
    : m_exp(exp), m_sig(sig)
{
}

floatingPointTypeInfo::floatingPointTypeInfo(const floatingPointTypeInfo& old)
    : m_exp(old.exponentWidth()), m_sig(old.significandWidth())
{
}

bitWidthType floatingPointTypeInfo::exponentWidth(void) const
{
  return m_exp;
}

bitWidthType floatingPointTypeInfo::significandWidth(void) const
{
  return m_sig;
}

bitWidthType floatingPointTypeInfo::packedWidth(void) const
{
  return exponentWidth() + significandWidth();
}

bitWidthType floatingPointTypeInfo::packedExponentWidth(void) const
{
  return exponentWidth();
}

bitWidthType floatingPointTypeInfo::packedSignificandWidth(void) const
{
  return significandWidth() - 1;
}

/****************************************************************
 * symfpu ITE dispatch                                          *
 ****************************************************************/

namespace symfpu
{

template <> struct ite<symbolic_fp::proposition, symbolic_fp::proposition>
{
  static const symbolic_fp::proposition
  iteOp(const symbolic_fp::proposition& cond,
        const symbolic_fp::proposition& l, const symbolic_fp::proposition& r)
  {
    return symbolic_fp::proposition(s_nf->CreateNode(stp::ITE, cond, l, r));
  }
};

#define STP_SYM_ITE_TERM(T)                                                    \
  template <> struct ite<symbolic_fp::proposition, T>                          \
  {                                                                            \
    static const T iteOp(const symbolic_fp::proposition& cond, const T& l,     \
                         const T& r)                                           \
    {                                                                          \
      assert(l.GetValueWidth() == r.GetValueWidth());                          \
      return T(s_nf->CreateTerm(stp::ITE, l.GetValueWidth(), cond, l, r));     \
    }                                                                          \
  }

STP_SYM_ITE_TERM(symbolic_fp::traits::rm);
STP_SYM_ITE_TERM(symbolic_fp::traits::sbv);
STP_SYM_ITE_TERM(symbolic_fp::traits::ubv);

#undef STP_SYM_ITE_TERM

// symfpu's divide path calls ITE with a literal bool condition rather than a
// proposition (core/divide.h, computing the result-exponent bounds), so the
// backend has to provide a bool-conditioned ITE as well. The condition is a
// compile-time constant, so this just selects a branch.
template <class T> struct ite<bool, T>
{
  static const T iteOp(const bool& cond, const T& l, const T& r)
  {
    return cond ? l : r;
  }
};

} // namespace symfpu

/****************************************************************
 * blast_*: one floating-point operation each                   *
 ****************************************************************/

namespace stp
{
namespace symbolic_fp
{

namespace
{
void assertUnpackedFormat(const floatingPointTypeInfo& size, const uf& value)
{
  assert(value.getExponent().getWidth() == uf::exponentWidth(size));
  assert(value.getSignificand().getWidth() == uf::significandWidth(size));
  (void)size;
  (void)value;
}
} // namespace

namespace unpacked
{

uf decode(const floatingPointTypeInfo& size, const ASTNode& packed)
{
  assert(packed.GetValueWidth() == size.packedWidth());
  return symfpu::unpack<traits>(size, packed);
}

ASTNode encode(const floatingPointTypeInfo& size, const uf& value)
{
  assertUnpackedFormat(size, value);
  return symfpu::pack<traits>(size, value);
}

uf select(const ASTNode& condition, const uf& when_true,
          const uf& when_false)
{
  assert(condition.GetType() == BOOLEAN_TYPE);
  assert(when_true.getExponent().getWidth() ==
         when_false.getExponent().getWidth());
  assert(when_true.getSignificand().getWidth() ==
         when_false.getSignificand().getWidth());
  return symfpu::ite<proposition, uf>::iteOp(
      proposition(condition), when_true, when_false);
}

ASTNode smtEqual(const floatingPointTypeInfo& size, const uf& lhs,
                 const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::smtlibEqual<traits>(size, lhs, rhs);
}

uf add(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& lhs,
       const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::add<traits>(size, rm, lhs, rhs, true);
}

uf sub(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& lhs,
       const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::add<traits>(size, rm, lhs, rhs, false);
}

uf mul(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& lhs,
       const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::multiply<traits>(size, rm, lhs, rhs);
}

uf div(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& lhs,
       const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::divide<traits>(size, rm, lhs, rhs);
}

uf fma(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& x,
       const uf& y, const uf& z)
{
  assertUnpackedFormat(size, x);
  assertUnpackedFormat(size, y);
  assertUnpackedFormat(size, z);
  return symfpu::fma<traits>(size, rm, x, y, z);
}

uf sqrt(const floatingPointTypeInfo& size, const ASTNode& rm, const uf& value)
{
  assertUnpackedFormat(size, value);
  return symfpu::sqrt<traits>(size, rm, value);
}

uf rem(const floatingPointTypeInfo& size, const uf& lhs, const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::remainder<traits>(size, lhs, rhs);
}

uf min(const floatingPointTypeInfo& size, const uf& lhs, const uf& rhs,
       const ASTNode& zero_case)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::min<traits>(size, lhs, rhs, proposition(zero_case));
}

uf max(const floatingPointTypeInfo& size, const uf& lhs, const uf& rhs,
       const ASTNode& zero_case)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::max<traits>(size, lhs, rhs, proposition(zero_case));
}

uf abs(const floatingPointTypeInfo& size, const uf& value)
{
  assertUnpackedFormat(size, value);
  return symfpu::absolute<traits>(size, value);
}

uf neg(const floatingPointTypeInfo& size, const uf& value)
{
  assertUnpackedFormat(size, value);
  return symfpu::negate<traits>(size, value);
}

uf roundToIntegral(const floatingPointTypeInfo& size, const ASTNode& rm,
                   const uf& value)
{
  assertUnpackedFormat(size, value);
  return symfpu::roundToIntegral<traits>(size, rm, value);
}

ASTNode toBV(const floatingPointTypeInfo& size, const ASTNode& rm,
             const uf& value, bitWidthType target_width,
             const ASTNode& undef, bool is_signed)
{
  assertUnpackedFormat(size, value);
  if (is_signed)
    return symfpu::convertFloatToSBV<traits>(size, rm, value, target_width,
                                             traits::sbv(undef));

  return symfpu::convertFloatToUBV<traits>(size, rm, value, target_width,
                                           traits::ubv(undef));
}

ASTNode ieeeEqual(const floatingPointTypeInfo& size, const uf& lhs,
                  const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::ieee754Equal<traits>(size, lhs, rhs);
}

ASTNode lessThan(const floatingPointTypeInfo& size, const uf& lhs,
                 const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::lessThan<traits>(size, lhs, rhs);
}

ASTNode lessThanOrEqual(const floatingPointTypeInfo& size, const uf& lhs,
                        const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);
  return symfpu::lessThanOrEqual<traits>(size, lhs, rhs);
}

ASTNode addIsZero(const floatingPointTypeInfo& size, const uf& lhs,
                  const uf& rhs)
{
  assertUnpackedFormat(size, lhs);
  assertUnpackedFormat(size, rhs);

  // Every finite value in one binary IEEE format is an integer multiple of
  // that format's minimum subnormal.  Consequently the exact sum of two
  // values in the format is either zero or has magnitude at least one
  // minimum subnormal: rounding cannot turn a nonzero sum into zero, in any
  // rounding mode.  Apart from two signed zeros, exact cancellation is
  // therefore precisely opposite signs and equal normalized magnitudes.
  //
  // Keep the class tests explicit.  The exponent and significand fields of
  // a SymFPU special value are harmless defaults, not part of that value's
  // semantics, and must never make an infinity or NaN look cancellable.
  const proposition finite =
      !lhs.getNaN() && !lhs.getInf() && !rhs.getNaN() && !rhs.getInf();
  const proposition bothZero = lhs.getZero() && rhs.getZero();
  const proposition neitherZero = !lhs.getZero() && !rhs.getZero();
  const proposition sameMagnitude =
      (lhs.getExponent() == rhs.getExponent()) &&
      (lhs.getSignificand() == rhs.getSignificand());
  const proposition cancellation =
      neitherZero && (lhs.getSign() ^ rhs.getSign()) && sameMagnitude;
  return finite && (bothZero || cancellation);
}

#define STP_UNPACKED_CLASSIFY(name, symfpu_fn)                                 \
  ASTNode name(const floatingPointTypeInfo& size, const uf& value)             \
  {                                                                            \
    assertUnpackedFormat(size, value);                                          \
    return symfpu::symfpu_fn<traits>(size, value);                              \
  }

STP_UNPACKED_CLASSIFY(isNormal, isNormal)
STP_UNPACKED_CLASSIFY(isSubnormal, isSubnormal)
STP_UNPACKED_CLASSIFY(isZero, isZero)
STP_UNPACKED_CLASSIFY(isInfinite, isInfinite)
STP_UNPACKED_CLASSIFY(isNaN, isNaN)
STP_UNPACKED_CLASSIFY(isNegative, isNegative)
STP_UNPACKED_CLASSIFY(isPositive, isPositive)

#undef STP_UNPACKED_CLASSIFY

uf convertBVToFloat(const floatingPointTypeInfo& target, const ASTNode& rm,
                    const ASTNode& bits, bool is_signed)
{
  return is_signed
             ? symfpu::convertSBVToFloat<traits>(target, rm, traits::sbv(bits))
             : symfpu::convertUBVToFloat<traits>(target, rm, traits::ubv(bits));
}

uf convertFloatToFloat(const floatingPointTypeInfo& source,
                       const floatingPointTypeInfo& target,
                       const ASTNode& rm, const uf& value)
{
  assertUnpackedFormat(source, value);
  return symfpu::convertFloatToFloat<traits>(source, target, rm, value);
}

} // namespace unpacked

// Instantiate both bit-vector flavours in full. symfpu only uses a subset of
// the interface, so without this the rest is never emitted and cannot be
// exercised from outside this file -- including by a test.
template class bitVector<true>;
template class bitVector<false>;

} // namespace symbolic_fp

} // namespace stp

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

#include "stp/FloatBlaster/symbolic_fp.h"

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"

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

using namespace stp;
using namespace stp::symbolic_fp;

stp::STPMgr* b;

typedef ::symfpu::unpackedFloat<traits> uf;

nodeWrapper::nodeWrapper(const Node& n) : Node(n) {}

roundingMode::roundingMode(unsigned int) : nodeWrapper(b->CreateBVConst(1, 1))
{
}

roundingMode::roundingMode(const Node n) : nodeWrapper(n) {}

roundingMode traits::RNE(void)
{
  return roundingMode(0x01);
}

roundingMode traits::RNA(void)
{
  return roundingMode(0x02);
}

roundingMode traits::RTP(void)
{
  return roundingMode(0x04);
}

roundingMode traits::RTN(void)
{
  return roundingMode(0x08);
}

roundingMode traits::RTZ(void)
{
  return roundingMode(0x10);
}

proposition roundingMode::operator==(const roundingMode& op) const
{
  return proposition(b->CreateNode(stp::EQ, *this, op));
}

void traits::precondition(const bool b)
{
  assert(b);
}

void traits::postcondition(const bool b)
{
  assert(b);
}

void traits::invariant(const bool b)
{
  assert(b);
}

void traits::precondition(const prop& p) {}

void traits::postcondition(const prop& p) {}

void traits::invariant(const prop& p) {}

proposition::proposition(const Node n) : nodeWrapper(n)
{
  assert(checkNodeType(*this));
}

proposition::proposition(bool v)
    : nodeWrapper(b->CreateNode(v ? stp::TRUE : stp::FALSE))
{
  assert(checkNodeType(*this));
}

proposition::proposition(const proposition& old) : nodeWrapper(old)
{
  assert(checkNodeType(*this));
}

bool proposition::checkNodeType(const TNode node)
{
  return node.GetType() == stp::BOOLEAN_TYPE;
}

proposition proposition::operator!(void) const
{
  return proposition(b->CreateNode(stp::NOT, *this));
}

proposition proposition::operator&&(const proposition& op) const
{
  return proposition(b->CreateNode(stp::AND, *this, op));
}

proposition proposition::operator||(const proposition& op) const
{
  return proposition(b->CreateNode(stp::OR, *this, op));
}

proposition proposition::operator==(const proposition& op) const
{
  return proposition(b->CreateNode(stp::IFF, *this, op));
}

proposition proposition::operator^(const proposition& op) const
{
  return proposition(b->CreateNode(stp::XOR, *this, op));
}

template <> bitVector<true> bitVector<true>::maxValue(const bitWidthType& w)
{
  bitVector<true> leadingZero(bitVector<true>::zero(1));
  bitVector<true> base(bitVector<true>::allOnes(w - 1));

  return bitVector<true>(b->CreateNode(stp::BVCONCAT, leadingZero, base));
}

template <> bitVector<false> bitVector<false>::maxValue(const bitWidthType& w)
{
  return bitVector<false>::allOnes(w);
}

template <> bitVector<true> bitVector<true>::minValue(const bitWidthType& w)
{
  bitVector<true> leadingOne(bitVector<true>::one(1));
  bitVector<true> base(bitVector<true>::zero(w - 1));

  return bitVector<true>(b->CreateNode(stp::BVCONCAT, leadingOne, base));
}

template <> bitVector<false> bitVector<false>::minValue(const bitWidthType& w)
{
  return bitVector<false>::zero(w);
}

template <bool isSigned>
bitVector<isSigned>::bitVector(const Node n) : nodeWrapper(n)
{
  assert(checkNodeType(*this));
}

template <bool isSigned> bool bitVector<isSigned>::checkNodeType(const TNode n)
{
  return GetType() == stp::BITVECTOR_TYPE;
}

template <bool isSigned>
bitVector<isSigned>::bitVector(const bitWidthType w, const unsigned v)
    : nodeWrapper(b->CreateBVConst(w, v))
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

template <bool isSigned> bitWidthType bitVector<isSigned>::getWidth(void) const
{
  return GetValueWidth();
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

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator<<(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVLEFTSHIFT, *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator>>(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(b->CreateNode(
      (isSigned) ? stp::BVSRSHIFT : stp::BVRIGHTSHIFT, *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator|(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVOR, *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator&(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVAND, *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator+(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVPLUS, *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator-(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVSUB, *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator*(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVMULT, *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator/(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(
      b->CreateNode((isSigned) ? stp::SBVDIV : stp::BVDIV, *this, op));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator%(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(
      b->CreateNode((isSigned) ? stp::SBVMOD : stp::BVMOD, *this, op));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::operator-(void) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVUMINUS, *this));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::operator~(void) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVNOT, *this));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::increment() const
{
  Node one(b->CreateBVConst(1, 1));
  return bitVector<isSigned>(b->CreateNode(stp::BVPLUS, *this, one));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::decrement() const
{
  Node one(b->CreateBVConst(1, 1));
  return bitVector<isSigned>(b->CreateNode(stp::BVUMINUS, *this, one));
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::signExtendRightShift(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVSRSHIFT, *this, op));
}

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
bitVector<isSigned> bitVector<isSigned>::modularNegate() const
{
  return -(*this);
}

template <bool isSigned>
proposition bitVector<isSigned>::operator==(const bitVector<isSigned>& op) const
{
  return proposition(b->CreateNode(stp::EQ, *this, op));
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
proposition bitVector<isSigned>::operator<(const bitVector<isSigned>& op) const
{
  return proposition(
      b->CreateNode((isSigned) ? stp::BVSLT : stp::BVLT, *this, op));
}

template <bool isSigned>
proposition bitVector<isSigned>::operator>(const bitVector<isSigned>& op) const
{
  return proposition(
      b->CreateNode((isSigned) ? stp::BVSLT : stp::BVLT, op, *this));
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
inline bitVector<true> bitVector<true>::extend(bitWidthType extension) const
{
  unsigned int nbits = this->getWidth() + extension;
  Node width(b->CreateBVConst(32, nbits));
  Node construct(b->CreateTerm(stp::BVSX, nbits, *this, width));
  return bitVector<true>(construct);
}

template <>
inline bitVector<false> bitVector<false>::extend(bitWidthType extension) const
{
  unsigned int nbits = this->getWidth() + extension;
  Node zero(b->CreateBVConst(1, extension));
  Node construct(b->CreateTerm(stp::BVCONCAT, nbits, zero, *this));
  return bitVector<false>(construct);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::contract(bitWidthType reduction) const
{
  assert(this->getWidth() > reduction);

  unsigned int width = (this->getWidth() - 1) - reduction;

  Node high(b->CreateBVConst(32, width));
  Node low(b->CreateBVConst(32, 0));
  Node construct(b->CreateTerm(stp::BVEXTRACT, width, *this, high, low));
  return bitVector<isSigned>(construct);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::resize(bitWidthType newSize) const
{
  bitWidthType width = this->getWidth();

  if (newSize > width)
  {
    return this->extend(newSize - width);
  }
  else if (newSize < width)
  {
    return this->contract(width - newSize);
  }
  else
  {
    return *this;
  }
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::matchWidth(const bitVector<isSigned>& op) const
{
  assert(this->getWidth() <= op.getWidth());
  return this->extend(op.getWidth() - this->getWidth());
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::append(const bitVector<isSigned>& op) const
{
  return bitVector<isSigned>(b->CreateNode(stp::BVCONCAT, *this, op));
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::extract(bitWidthType upper,
                                                 bitWidthType lower) const
{
  assert(upper >= lower);

  unsigned int width = upper - lower;
  Node high(b->CreateBVConst(32, upper));
  Node low(b->CreateBVConst(32, lower));
  Node construct(b->CreateTerm(stp::BVEXTRACT, width, *this, high, low));
  return bitVector<isSigned>(construct);
}

template <bool isSigned>
Node bitVector<isSigned>::fromProposition(Node node) const
{
#ifdef PROPSYMFPUISBOOL
  return boolNodeToBV(node);
#else
  return node;
#endif
}

floatingPointTypeInfo::floatingPointTypeInfo(const TypeNode t) : TypeNode(t)
{
  assert(GetType() == stp::FLOATINGPOINT_TYPE);
}

floatingPointTypeInfo::floatingPointTypeInfo(unsigned exp, unsigned sig)
    : TypeNode()
{
}

floatingPointTypeInfo::floatingPointTypeInfo(const floatingPointTypeInfo& old)
    : TypeNode(old)
{
}

bitWidthType floatingPointTypeInfo::exponentWidth(void) const
{
  return GetExpWidth();
}

bitWidthType floatingPointTypeInfo::significandWidth(void) const
{
  return GetSigWidth();
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

TypeNode floatingPointTypeInfo::getTypeNode(void) const
{
  return *this;
}

#ifdef SYMFPUPROPISBOOL
#define STPSYMITEDFN(T)                                                        \
  template <> struct symfpu::ite<symbolic_fp::proposition, T>                  \
  {                                                                            \
    static const T iteOp(const symbolic_fp::proposition& cond, const T& l,     \
                         const T& r)                                           \
    {                                                                          \
      return T(b->CreateNode(stp::ITE, cond, l, r));                           \
    }                                                                          \
  }

#else
#define STPSYMITEDFN(T)                                                        \
  template <> struct symfpu::ite<symbolic_fp::proposition, T>                  \
  {                                                                            \
    static const T iteOp(const symbolic_fp::proposition& _cond, const T& _l,   \
                         const T& _r)                                          \
    {                                                                          \
      ASTNode cond = _cond;                                                    \
      ASTNode l = _l;                                                          \
      ASTNode r = _r;                                                          \
                                                                               \
      if (cond.GetKind() == stp::BVCONST)                                      \
      {                                                                        \
        if (cond == b->CreateBVConst(1U, 1U))                                  \
        {                                                                      \
          return l;                                                            \
        }                                                                      \
        else                                                                   \
        {                                                                      \
          return r;                                                            \
        }                                                                      \
      }                                                                        \
      else                                                                     \
      {                                                                        \
        if (l.GetKind() == stp::ITE)                                           \
        {                                                                      \
          if (l[1] == r)                                                       \
          {                                                                    \
            return b->CreateNode(                                              \
                stp::ITE,                                                      \
                b->CreateNode(stp::BVAND, cond,                                \
                              b->CreateNode(stp::BVNOT, l[0])),                \
                l[2], r);                                                      \
          }                                                                    \
          else if (l[2] == r)                                                  \
          {                                                                    \
            return b->CreateNode(                                              \
                stp::ITE, b->CreateNode(stp::BVAND, cond, l[0]), l[1], r);     \
          }                                                                    \
        }                                                                      \
        else if (r.GetKind() == stp::ITE)                                      \
        {                                                                      \
          if (r[1] == l)                                                       \
          {                                                                    \
            return b->CreateNode(                                              \
                stp::ITE,                                                      \
                b->CreateNode(stp::BVAND, b->CreateNode(stp::BVNOT, cond),     \
                              b->CreateNode(stp::BVNOT, r[0])),                \
                r[2], l);                                                      \
          }                                                                    \
          else if (r[2] == l)                                                  \
          {                                                                    \
            return b->CreateNode(                                              \
                stp::ITE,                                                      \
                b->CreateNode(stp::BVAND, b->CreateNode(stp::BVNOT, cond),     \
                              r[0]),                                           \
                r[1], l);                                                      \
          }                                                                    \
        }                                                                      \
      }                                                                        \
      return T(b->CreateNode(stp::ITE, cond, l, r));                           \
    }                                                                          \
  }

#endif

STPSYMITEDFN(symbolic_fp::traits::rm);
STPSYMITEDFN(symbolic_fp::traits::prop);
STPSYMITEDFN(symbolic_fp::traits::sbv);
STPSYMITEDFN(symbolic_fp::traits::ubv);

#undef STPSYMITEDFN

void foo(roundingMode rm, uf a1, uf a2, floatingPointTypeInfo size)
{
  uf* moo = new uf(symfpu::add<traits>(size, rm, a1, a2, true));
}

// EOF

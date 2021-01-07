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
#include "stp/c_interface.h"

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

#define SYMFPUPROPISBOOL

using namespace stp;
using namespace stp::symbolic_fp;

VC vc;

typedef ::symfpu::unpackedFloat<traits> uf;

nodeWrapper::nodeWrapper(const Node& n) : Node(n) {}

roundingMode::roundingMode(unsigned int v)
    : nodeWrapper(*static_cast<Node*>(
          vc_bvConstExprFromInt(vc, SYMFPU_NUMBER_OF_ROUNDING_MODES, v)))
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
  void* vs_this = reinterpret_cast<void*>(const_cast<roundingMode*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<roundingMode*>(&op));
  void* expr = vc_eqExpr(vc, vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return proposition(*node);
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
    : nodeWrapper(v ? *static_cast<Node*>(vc_trueExpr(vc))
                    : *static_cast<Node*>(vc_falseExpr(vc)))
{
  assert(checkNodeType(*this));
}

proposition::proposition(const proposition& old) : nodeWrapper(old)
{
  assert(checkNodeType(*this));
}

bool proposition::checkNodeType(const TNode node)
{
  bool result(node.GetType() == stp::BOOLEAN_TYPE);
  assert(result);
  return result;
}

proposition proposition::operator!(void) const
{
  void* vs_this = reinterpret_cast<void*>(const_cast<proposition*>(this));
  void* expr = vc_notExpr(vc, vs_this);
  Node* node = static_cast<Node*>(expr);
  return proposition(*node);
}

proposition proposition::operator&&(const proposition& op) const
{
  void* vs_this = reinterpret_cast<void*>(const_cast<proposition*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<proposition*>(&op));
  void* expr = vc_andExpr(vc, vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return proposition(*node);
}

proposition proposition::operator||(const proposition& op) const
{
  void* vs_this = reinterpret_cast<void*>(const_cast<proposition*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<proposition*>(&op));
  void* expr = vc_orExpr(vc, vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return proposition(*node);
}

proposition proposition::operator==(const proposition& op) const
{
  void* vs_this = reinterpret_cast<void*>(const_cast<proposition*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<proposition*>(&op));
  void* expr = vc_eqExpr(vc, vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return proposition(*node);
}

proposition proposition::operator^(const proposition& op) const
{
  void* vs_this = reinterpret_cast<void*>(const_cast<proposition*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<proposition*>(&op));
  void* expr = vc_xorExpr(vc, vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return proposition(*node);
}

template <> bitVector<true> bitVector<true>::maxValue(const bitWidthType& w)
{
  bitVector<true> leadingZero(bitVector<true>::zero(1));
  bitVector<true> base(bitVector<true>::allOnes(w - 1));

  void* vs_leading =
      reinterpret_cast<void*>(const_cast<bitVector<true>*>(&leadingZero));
  void* vs_base = reinterpret_cast<void*>(const_cast<bitVector<true>*>(&base));
  void* expr = vc_bvConcatExpr(vc, vs_leading, vs_base);
  Node* node = static_cast<Node*>(expr);
  assert(node->GetValueWidth() > 0);
  return bitVector<true>(*node);
}

template <> bitVector<false> bitVector<false>::maxValue(const bitWidthType& w)
{
  return bitVector<false>::allOnes(w);
}

template <> bitVector<true> bitVector<true>::minValue(const bitWidthType& w)
{
  bitVector<true> leadingZero(bitVector<true>::zero(1));
  bitVector<true> base(bitVector<true>::zero(w - 1));

  void* vs_leading =
      reinterpret_cast<void*>(const_cast<bitVector<true>*>(&leadingZero));
  void* vs_base = reinterpret_cast<void*>(const_cast<bitVector<true>*>(&base));
  void* expr = vc_bvConcatExpr(vc, vs_leading, vs_base);
  Node* node = static_cast<Node*>(expr);
  assert(node->GetValueWidth() > 0);
  return bitVector<true>(*node);
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
  bool result(n.GetType() == stp::BITVECTOR_TYPE ||
              n.GetType() == stp::FLOATINGPOINT_TYPE);
  if (!result)
  {
    std::cout << GetValueWidth() << std::endl;
    std::cout << n << std::endl;
  }
  assert(result);
  assert(GetValueWidth() > 0);
  return result;
}

template <bool isSigned>
bitVector<isSigned>::bitVector(const bitWidthType w, const unsigned v)
    : nodeWrapper(*static_cast<Node*>(vc_bvConstExprFromInt(vc, w, v)))
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
  bitWidthType ret = 0;
  if (GetType() == BOOLEAN_TYPE)
  {
    ret = 1;
  }
  else
  {
    ret = GetValueWidth();
  }
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

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator<<(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = vc_bvLeftShiftExprExpr(vc, GetValueWidth(), vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator>>(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = nullptr;
  if (isSigned)
  {
    expr = vc_bvSignedRightShiftExprExpr(vc, GetValueWidth(), vs_this, vs_op);
  }
  else
  {
    expr = vc_bvRightShiftExprExpr(vc, GetValueWidth(), vs_this, vs_op);
  }
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator|(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = vc_bvOrExpr(vc, vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator&(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = vc_bvAndExpr(vc, vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator+(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = vc_bvPlusExpr(vc, GetValueWidth(), vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator-(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = vc_bvMinusExpr(vc, GetValueWidth(), vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator*(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = vc_bvMultExpr(vc, GetValueWidth(), vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator/(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = nullptr;
  if (isSigned)
  {
    expr = vc_sbvDivExpr(vc, GetValueWidth(), vs_this, vs_op);
  }
  else
  {
    expr = vc_bvDivExpr(vc, GetValueWidth(), vs_this, vs_op);
  }
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::operator%(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = nullptr;
  if (isSigned)
  {
    expr = vc_sbvModExpr(vc, GetValueWidth(), vs_this, vs_op);
  }
  else
  {
    expr = vc_bvModExpr(vc, GetValueWidth(), vs_this, vs_op);
  }
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::operator-(void) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* expr = vc_bvUMinusExpr(vc, vs_this);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::operator~(void) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* expr = vc_bvNotExpr(vc, vs_this);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::increment() const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* one = vc_bvConstExprFromInt(vc, GetValueWidth(), 1);
  void* expr = vc_bvPlusExpr(vc, GetValueWidth(), vs_this, one);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::decrement() const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* one = vc_bvConstExprFromInt(vc, GetValueWidth(), 1);
  void* expr = vc_bvMinusExpr(vc, GetValueWidth(), vs_this, one);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::signExtendRightShift(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr =
      vc_bvSignedRightShiftExprExpr(vc, GetValueWidth(), vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
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
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = vc_eqExpr(vc, vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return proposition(*node);
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
  const bitVector<isSigned> this_node(*this);
  bitWidthType this_size = this_node.GetValueWidth();
  const bitVector<isSigned> op_node(op);
  bitWidthType op_size = op_node.GetValueWidth();

  const bitVector<isSigned>* lhs = nullptr;
  const bitVector<isSigned>* rhs = nullptr;

  if (this_size > op_size)
  {
    lhs = this;
    rhs = new bitVector<isSigned>(op_node.matchWidth(this_node));
  }
  else if (op_size > this_size)
  {
    lhs = new bitVector<isSigned>(this_node.matchWidth(op_node));
    rhs = &op;
  }
  else
  {
    lhs = this;
    rhs = &op;
  }

  assert(lhs->GetValueWidth() == rhs->GetValueWidth());

  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(lhs));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(rhs));
  void* expr = nullptr;
  if (isSigned)
  {
    expr = vc_sbvLtExpr(vc, vs_this, vs_op);
  }
  else
  {
    expr = vc_bvLtExpr(vc, vs_this, vs_op);
  }
  Node* node = static_cast<Node*>(expr);
  return proposition(*node);
}

template <bool isSigned>
proposition bitVector<isSigned>::operator>(const bitVector<isSigned>& op) const
{
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = nullptr;
  if (isSigned)
  {
    expr = vc_sbvLtExpr(vc, vs_op, vs_this);
  }
  else
  {
    expr = vc_bvLtExpr(vc, vs_op, vs_this);
  }
  Node* node = static_cast<Node*>(expr);
  return proposition(*node);
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
  void* vs_this = reinterpret_cast<void*>(const_cast<bitVector<true>*>(this));
  bitWidthType new_length = this->GetValueWidth() + extension;
  void* expr = vc_bvSignExtend(vc, vs_this, new_length);
  Node* node = static_cast<Node*>(expr);
  bitVector<true> ret(*node);
  assert(ret.GetValueWidth() == this->GetValueWidth() + extension);
  return ret;
}

template <>
inline bitVector<false> bitVector<false>::extend(bitWidthType extension) const
{
  void* vs_this = reinterpret_cast<void*>(const_cast<bitVector<false>*>(this));
  void* zero = vc_bvConstExprFromInt(vc, extension, 0);
  void* expr = vc_bvConcatExpr(vc, vs_this, zero);
  Node* node = static_cast<Node*>(expr);
  assert(node->GetValueWidth() > 0);
  bitVector<true> ret(*node);
  assert(ret.GetValueWidth() == this->GetValueWidth() + extension);
  return ret;
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::contract(bitWidthType reduction) const
{
  assert(this->getWidth() > reduction);

  unsigned int width = (this->getWidth() - 1) - reduction;

  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* expr = vc_bvExtract(vc, vs_this, width, 0);
  Node* node = static_cast<Node*>(expr);
  return bitVector<false>(*node);
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
  if (this->getWidth() == op.getWidth())
  {
    return *this;
  }
  else
  {
    bitWidthType to_add = op.getWidth() - this->getWidth();
    assert(op.getWidth() == to_add + this->getWidth());
    bitVector<isSigned> ret(this->extend(to_add));
    assert(ret.getWidth() == to_add + this->getWidth());
    return ret;
  }
}

template <bool isSigned>
bitVector<isSigned>
bitVector<isSigned>::append(const bitVector<isSigned>& op) const
{
  if (GetValueWidth() <= 0)
  {
    std::cout << *this << std::endl;
    assert(false);
  }
  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* vs_op = reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(&op));
  void* expr = vc_bvConcatExpr(vc, vs_this, vs_op);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
bitVector<isSigned> bitVector<isSigned>::extract(bitWidthType upper,
                                                 bitWidthType lower) const
{
  assert(upper >= lower);

  void* vs_this = reinterpret_cast<void*>(const_cast<bitVector<false>*>(this));
  void* expr = vc_bvExtract(vc, vs_this, upper, lower);
  Node* node = static_cast<Node*>(expr);
  return bitVector<isSigned>(*node);
}

template <bool isSigned>
Node bitVector<isSigned>::fromProposition(Node node) const
{
#ifdef SYMFPUPROPISBOOL
  void* vs_node = reinterpret_cast<void*>(&node);
  void* zero = vc_bvConstExprFromInt(vc, 1, 0);
  void* one = vc_bvConstExprFromInt(vc, 1, 1);
  void* expr = vc_iteExpr(vc, vs_node, one, zero);
  Node* result = static_cast<Node*>(expr);
  return bitVector<isSigned>(*result);
#else
  return node;
#endif
}

floatingPointTypeInfo::floatingPointTypeInfo(const TypeNode t) : TypeNode(t)
{
  assert(t.GetType() == stp::FLOATINGPOINT_TYPE);
}

floatingPointTypeInfo::floatingPointTypeInfo(unsigned exp, unsigned sig)
    : TypeNode(*static_cast<Node*>(vc_bvConstExprFromInt(vc, 1, 1)))
{
  SetExpWidth(exp);
  SetSigWidth(sig);
  assert(GetType() == stp::FLOATINGPOINT_TYPE);
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
      assert(l.GetValueWidth() == r.GetValueWidth());                          \
      Expr ite_expr = vc_iteExpr(vc, (Expr)&cond, (Expr)&l, (Expr)&r);         \
      return *(T*)ite_expr;                                                    \
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
        if (cond == *(Node*)vc_bvConstExprFromInt(vc, 1, 1))                   \
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
            Expr not_expr = vc_bvNotExpr(vc, (Expr)&l[0]);                     \
            Expr and_expr = vc_andExpr(vc, (Expr)&cond, not_expr);             \
            Expr ite_expr = vc_iteExpr(vc, and_expr, (Expr)&l[2], (Expr)&r);   \
            return *(T*)ite_expr;                                              \
          }                                                                    \
          else if (l[2] == r)                                                  \
          {                                                                    \
            Expr and_expr = vc_andExpr(vc, (Expr)&cond, (Expr)(&l[0]));        \
            Expr ite_expr = vc_iteExpr(vc, and_expr, (Expr)&l[1], (Expr)&r);   \
            return *(T*)ite_expr;                                              \
          }                                                                    \
        }                                                                      \
        else if (r.GetKind() == stp::ITE)                                      \
        {                                                                      \
          if (r[1] == l)                                                       \
          {                                                                    \
            Expr not_cond = vc_bvNotExpr(vc, (Expr)&cond);                     \
            Expr not_r = vc_bvNotExpr(vc, (Expr)&r[0]);                        \
            Expr and_expr = vc_andExpr(vc, not_cond, not_r);                   \
            Expr ite_expr = vc_iteExpr(vc, and_expr, (Expr)&r[2], (Expr)&l);   \
            return *(T*)ite_expr;                                              \
          }                                                                    \
          else if (r[2] == l)                                                  \
          {                                                                    \
            Expr not_cond = vc_bvNotExpr(vc, (Expr)&cond);                     \
            Expr and_expr = vc_andExpr(vc, not_cond, (Expr)&r[0]);             \
            Expr ite_expr = vc_iteExpr(vc, and_expr, (Expr)&r[1], (Expr)&l);   \
            return *(T*)ite_expr;                                              \
          }                                                                    \
        }                                                                      \
      }                                                                        \
      Expr ite_expr = vc_iteExpr(vc, (Expr)&cond, (Expr)&l, (Expr)&r);         \
      return *(T*)ite_expr;                                                    \
    }                                                                          \
  }

#endif

STPSYMITEDFN(symbolic_fp::traits::rm);
STPSYMITEDFN(symbolic_fp::traits::prop);
STPSYMITEDFN(symbolic_fp::traits::sbv);
STPSYMITEDFN(symbolic_fp::traits::ubv);

#undef STPSYMITEDFN

extern void foo(STPMgr* bm_p)
{
  vc = vc_createValidityChecker();

  int indexWidth(0);
  int valueWidth(32);
  Expr s1_expr =
      vc_varExpr1(vc, std::string("s1").c_str(), indexWidth, valueWidth);
  Node s1(*static_cast<Node*>(s1_expr));
  s1.SetExpWidth(8);
  s1.SetSigWidth(24);

  Expr s2_expr =
      vc_varExpr1(vc, std::string("s2").c_str(), indexWidth, valueWidth);
  Node s2(*static_cast<Node*>(s2_expr));
  s2.SetExpWidth(8);
  s2.SetSigWidth(24);

  Expr underlying_size_expr = vc_varExpr1(
      vc, std::string("underlying_size").c_str(), indexWidth, valueWidth);
  Node underlying_size(*static_cast<Node*>(underlying_size_expr));
  underlying_size.SetExpWidth(8);
  underlying_size.SetSigWidth(24);

  floatingPointTypeInfo size(underlying_size);

  uf a1(symfpu::unpack<traits>(size, s1));
  uf a2(symfpu::unpack<traits>(size, s2));

  roundingMode rm = traits::RNE();

  uf add(symfpu::add<traits>(size, rm, a1, a2, true));

  stp::ASTNode* res = new stp::ASTNode(symfpu::pack<traits>(size, add));

  stp::ASTNode* bvc = (stp::ASTNode*)vc_bvConstExprFromInt(vc, 32, 10);

  std::cout << res->GetType() << std::endl;
  std::cout << res->GetKind() << std::endl;
  std::cout << bvc->GetType() << std::endl;
  std::cout << bvc->GetKind() << std::endl;

  stp::ASTNode* expr = (stp::ASTNode*)vc_eqExpr(vc, res, bvc);

  std::cout << expr->GetKind() << std::endl;
  std::cout << expr->GetType() << std::endl;

  vc_query(vc, expr);
}

// EOF

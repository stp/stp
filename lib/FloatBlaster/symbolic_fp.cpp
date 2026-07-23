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

static VC vc;
static STPMgr* bm;

nodeWrapper::nodeWrapper(const Node& n) : Node(n) {}

roundingMode::roundingMode(unsigned int v)
    : nodeWrapper(*static_cast<Node*>(
          vc_bvConstExprFromInt(vc, SYMFPU_NUMBER_OF_ROUNDING_MODES, v)))
{
}

roundingMode::roundingMode(const Node n) : nodeWrapper(n) {}

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
  assert(GetType() == stp::BOOLEAN_TYPE);
  assert(op.GetType() == stp::BOOLEAN_TYPE);

  void* one = vc_bvConstExprFromInt(vc, 1, 1);
  void* zero = vc_bvConstExprFromInt(vc, 1, 0);

  void* vs_this = reinterpret_cast<void*>(const_cast<proposition*>(this));
  void* ite_this = vc_iteExpr(vc, vs_this, one, zero);

  void* vs_op = reinterpret_cast<void*>(const_cast<proposition*>(&op));
  void* ite_op = vc_iteExpr(vc, vs_op, one, zero);

  void* expr = vc_eqExpr(vc, ite_this, ite_op);

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
  assert(node->GetValueWidth() == w);
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
  assert(node->GetValueWidth() == w);
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
  // Extending by nothing is the identity. Falling through would ask for a
  // zero-width constant to concatenate, which STP rejects. symfpu's
  // conversion path does call this with an extension of zero.
  if (extension == 0)
    return *this;

  void* vs_this = reinterpret_cast<void*>(const_cast<bitVector<false>*>(this));
  void* zero = vc_bvConstExprFromInt(vc, extension, 0);
  void* expr = vc_bvConcatExpr(vc, zero, vs_this);
  Node* node = static_cast<Node*>(expr);
  assert(node->GetValueWidth() > 0);
  bitVector<false> ret(*node);
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
  return bitVector<isSigned>(*node);
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

  void* vs_this =
      reinterpret_cast<void*>(const_cast<bitVector<isSigned>*>(this));
  void* expr = vc_bvExtract(vc, vs_this, upper, lower);
  Node* node = static_cast<Node*>(expr);
  bitVector<isSigned> ret(*node);
  unsigned int expected_width = (upper - lower) + 1;
  assert(ret.GetValueWidth() == expected_width);
  return ret;
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

// symfpu's divide path calls ITE with a literal bool condition rather than a
// proposition (core/divide.h, computing the result-exponent bounds), so the
// backend has to provide a bool-conditioned ITE as well. The condition is a
// compile-time constant, so this just selects a branch.
namespace symfpu
{
template <class T> struct ite<bool, T>
{
  static const T iteOp(const bool& cond, const T& l, const T& r)
  {
    return cond ? l : r;
  }
};
}

namespace stp
{
namespace symbolic_fp
{

void init_vc(STPMgr* _bm)
{
  static bool init = false;
  if (!init)
  {
    init = true;
    vc = vc_createValidityCheckerReuse(_bm);
    bm = _bm;
  }
}

ASTNode blast_smt_eq(const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());

  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  proposition eq =
      symfpu::smtlibEqual<traits>(size, unpacked_lhs, unpacked_rhs);

  return eq;
}

ASTNode blast_fpadd(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  uf unpacked_add(
      symfpu::add<traits>(size, rm, unpacked_lhs, unpacked_rhs, true));

  ASTNode packed(symfpu::pack<traits>(size, unpacked_add));

  return packed;
}

// fp.sub is fp.add with the isAdd flag cleared: symfpu negates the right
// operand internally, which gets the -0/+0 and NaN corner cases right in a
// way that blasting (add lhs (neg rhs)) would not.
ASTNode blast_fpsub(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetSigWidth() == rhs.GetSigWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  uf unpacked_sub(
      symfpu::add<traits>(size, rm, unpacked_lhs, unpacked_rhs, false));

  ASTNode packed(symfpu::pack<traits>(size, unpacked_sub));

  return packed;
}

ASTNode blast_fpmul(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetSigWidth() == rhs.GetSigWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  uf unpacked_mul(
      symfpu::multiply<traits>(size, rm, unpacked_lhs, unpacked_rhs));

  ASTNode packed(symfpu::pack<traits>(size, unpacked_mul));

  return packed;
}

ASTNode blast_fpdiv(const ASTNode& rm, const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetSigWidth() == rhs.GetSigWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  uf unpacked_div(symfpu::divide<traits>(size, rm, unpacked_lhs, unpacked_rhs));

  ASTNode packed(symfpu::pack<traits>(size, unpacked_div));

  return packed;
}

ASTNode blast_fpfma(const ASTNode& rm, const ASTNode& x, const ASTNode& y,
                    const ASTNode& z)
{
  assert(x.GetExpWidth() == y.GetExpWidth());
  assert(x.GetSigWidth() == y.GetSigWidth());
  assert(x.GetExpWidth() == z.GetExpWidth());
  assert(x.GetSigWidth() == z.GetSigWidth());
  floatingPointTypeInfo size(x.GetExpWidth(), x.GetSigWidth());
  uf unpacked_x(symfpu::unpack<traits>(size, x));
  uf unpacked_y(symfpu::unpack<traits>(size, y));
  uf unpacked_z(symfpu::unpack<traits>(size, z));

  uf result(
      symfpu::fma<traits>(size, rm, unpacked_x, unpacked_y, unpacked_z));

  ASTNode packed(symfpu::pack<traits>(size, result));

  return packed;
}

ASTNode blast_fpsqrt(const ASTNode& rm, const ASTNode& expr)
{
  floatingPointTypeInfo size(expr.GetExpWidth(), expr.GetSigWidth());
  uf unpacked(symfpu::unpack<traits>(size, expr));
  uf result(symfpu::sqrt<traits>(size, rm, unpacked));
  ASTNode packed(symfpu::pack<traits>(size, result));
  return packed;
}

// fp.rem takes no rounding mode: the remainder is always exact, so there is
// nothing to round. symfpu's remainder() rounds with RNE internally only for
// the intermediate quotient.
ASTNode blast_fprem(const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetSigWidth() == rhs.GetSigWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  uf result(symfpu::remainder<traits>(size, unpacked_lhs, unpacked_rhs));

  ASTNode packed(symfpu::pack<traits>(size, result));

  return packed;
}

// fp.min/fp.max are unspecified when the arguments are +0 and -0: SMT-LIB
// says either zero may be returned, as does IEEE-754. symfpu takes that
// choice as its `zeroCase` argument; passing false makes the tie resolve
// towards the left operand, which is a conforming choice and, unlike an
// unconstrained one, keeps the result deterministic.
ASTNode blast_fpmin(const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetSigWidth() == rhs.GetSigWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  uf result(symfpu::min<traits>(size, unpacked_lhs, unpacked_rhs,
                                proposition(false)));

  ASTNode packed(symfpu::pack<traits>(size, result));

  return packed;
}

ASTNode blast_fpmax(const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetSigWidth() == rhs.GetSigWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  uf result(symfpu::max<traits>(size, unpacked_lhs, unpacked_rhs,
                                proposition(false)));

  ASTNode packed(symfpu::pack<traits>(size, result));

  return packed;
}

// fp.abs and fp.neg only touch the sign bit, but they go through unpack/pack
// anyway so that the NaN and infinity encodings stay canonical.
ASTNode blast_fpabs(const ASTNode& expr)
{
  floatingPointTypeInfo size(expr.GetExpWidth(), expr.GetSigWidth());
  uf unpacked(symfpu::unpack<traits>(size, expr));
  uf result(symfpu::absolute<traits>(size, unpacked));
  ASTNode packed(symfpu::pack<traits>(size, result));
  return packed;
}

ASTNode blast_fpneg(const ASTNode& expr)
{
  floatingPointTypeInfo size(expr.GetExpWidth(), expr.GetSigWidth());
  uf unpacked(symfpu::unpack<traits>(size, expr));
  uf result(symfpu::negate<traits>(size, unpacked));
  ASTNode packed(symfpu::pack<traits>(size, result));
  return packed;
}

// The classification predicates. Each returns a Boolean-typed node.
#define STP_BLAST_CLASSIFY(name, symfpu_fn)                                    \
  ASTNode name(const ASTNode& expr)                                            \
  {                                                                            \
    floatingPointTypeInfo size(expr.GetExpWidth(), expr.GetSigWidth());        \
    uf unpacked(symfpu::unpack<traits>(size, expr));                           \
    proposition result(symfpu::symfpu_fn<traits>(size, unpacked));             \
    return result;                                                             \
  }

STP_BLAST_CLASSIFY(blast_is_normal, isNormal)
STP_BLAST_CLASSIFY(blast_is_subnormal, isSubnormal)
STP_BLAST_CLASSIFY(blast_is_zero, isZero)
STP_BLAST_CLASSIFY(blast_is_infinite, isInfinite)
STP_BLAST_CLASSIFY(blast_is_nan, isNaN)
STP_BLAST_CLASSIFY(blast_is_negative, isNegative)
STP_BLAST_CLASSIFY(blast_is_positive, isPositive)

#undef STP_BLAST_CLASSIFY

// fp.eq is IEEE-754 equality, which differs from SMT-LIB's `=` on floats:
// NaN is equal to nothing including itself, and +0 equals -0. blast_smt_eq
// implements the latter (bit-identical) relation.
ASTNode blast_fpeq(const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetSigWidth() == rhs.GetSigWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  proposition eq(
      symfpu::ieee754Equal<traits>(size, unpacked_lhs, unpacked_rhs));

  return eq;
}

// The ordering predicates are the IEEE-754 ones, so they are false whenever
// either operand is NaN. symfpu's ordering() handles that; we just hand back
// the resulting proposition, which is already a Boolean-typed node.
ASTNode blast_fplt(const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetSigWidth() == rhs.GetSigWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  proposition lt(
      symfpu::lessThan<traits>(size, unpacked_lhs, unpacked_rhs));

  return lt;
}

ASTNode blast_fpleq(const ASTNode& lhs, const ASTNode& rhs)
{
  assert(lhs.GetValueWidth() == rhs.GetValueWidth());
  assert(lhs.GetExpWidth() == rhs.GetExpWidth());
  assert(lhs.GetSigWidth() == rhs.GetSigWidth());
  floatingPointTypeInfo size(lhs.GetExpWidth(), lhs.GetSigWidth());
  uf unpacked_lhs(symfpu::unpack<traits>(size, lhs));
  uf unpacked_rhs(symfpu::unpack<traits>(size, rhs));

  proposition leq(
      symfpu::lessThanOrEqual<traits>(size, unpacked_lhs, unpacked_rhs));

  return leq;
}

// ((_ to_fp e s) bv) reinterprets a bitvector's bits as a float. Floats are
// stored packed, so this is very nearly the identity -- but it must not
// return the child node itself. The exponent/significand widths live on the
// node, and the caller stamps them onto whatever comes back, which would
// retype the shared bitvector for every other use of it. Round-tripping
// through unpack/pack yields a distinct node, and canonicalises the NaN
// payloads that SMT-LIB leaves unspecified here.
ASTNode blast_reinterpret(const ASTNode& bits, bitWidthType exp_width,
                          bitWidthType sig_width)
{
  floatingPointTypeInfo size(exp_width, sig_width);
  uf unpacked(symfpu::unpack<traits>(size, bits));
  ASTNode packed(symfpu::pack<traits>(size, unpacked));
  return packed;
}

// ((_ to_fp e s) rm bv) reads the bitvector as a two's-complement integer,
// ((_ to_fp_unsigned e s) rm bv) as an unsigned one, and rounds it into the
// target format. Distinct from the one-argument form, which reinterprets the
// bits rather than converting the value they denote.
ASTNode blast_convert_bv_to_float(const ASTNode& rm, const ASTNode& bits,
                                  bitWidthType exp_width,
                                  bitWidthType sig_width, bool is_signed)
{
  floatingPointTypeInfo target(exp_width, sig_width);

  uf converted(is_signed ? symfpu::convertSBVToFloat<traits>(
                               target, rm, traits::sbv(bits))
                         : symfpu::convertUBVToFloat<traits>(
                               target, rm, traits::ubv(bits)));

  ASTNode packed(symfpu::pack<traits>(target, converted));

  return packed;
}

ASTNode blast_convert_float_to_float(const ASTNode& rm, const ASTNode& expr,
                                     bitWidthType target_exp,
                                     bitWidthType target_sig)
{
  floatingPointTypeInfo source(expr.GetExpWidth(), expr.GetSigWidth());
  floatingPointTypeInfo target(target_exp, target_sig);

  uf unpacked(symfpu::unpack<traits>(source, expr));
  uf converted(
      symfpu::convertFloatToFloat<traits>(source, target, rm, unpacked));

  ASTNode packed(symfpu::pack<traits>(target, converted));

  return packed;
}

ASTNode blast_pos_inf(const ASTNode& orig)
{
  floatingPointTypeInfo size(orig.GetExpWidth(), orig.GetSigWidth());
  uf unpacked_inf(uf::makeInf(size, false));
  ASTNode packed(symfpu::pack<traits>(size, unpacked_inf));
  return packed;
}

ASTNode blast_neg_inf(const ASTNode& orig)
{
  floatingPointTypeInfo size(orig.GetExpWidth(), orig.GetSigWidth());
  uf unpacked_inf(uf::makeInf(size, true));
  ASTNode packed(symfpu::pack<traits>(size, unpacked_inf));
  return packed;
}

ASTNode blast_nan(const ASTNode& orig)
{
  floatingPointTypeInfo size(orig.GetExpWidth(), orig.GetSigWidth());
  uf unpacked_nan(uf::makeNaN(size));
  ASTNode packed(symfpu::pack<traits>(size, unpacked_nan));
  return packed;
}

ASTNode blast_zero(const ASTNode& orig, bool sign)
{
  floatingPointTypeInfo size(orig.GetExpWidth(), orig.GetSigWidth());
  uf unpacked_zero(uf::makeZero(size, sign));
  ASTNode packed(symfpu::pack<traits>(size, unpacked_zero));
  return packed;
}

ASTNode round_trip(const ASTNode& expr, ASTNode** side)
{
  floatingPointTypeInfo size(expr.GetExpWidth(), expr.GetSigWidth());
  uf unpacked(symfpu::unpack<traits>(size, expr));
  *side = new ASTNode(unpacked.valid(size));
  ASTNode packed(symfpu::pack<traits>(size, unpacked));
  return packed;
}

ASTNode blast_round_to_integral(const ASTNode& rm, const ASTNode& expr)
{
  floatingPointTypeInfo size(expr.GetExpWidth(), expr.GetSigWidth());
  uf unpacked(symfpu::unpack<traits>(size, expr));
  uf unpacked_result(
      symfpu::roundToIntegral<traits>(size, rm, unpacked));
  ASTNode packed(symfpu::pack<traits>(size, unpacked_result));
  return packed;
}

} // namespace symbolic_fp

} // namespace stp

// EOF

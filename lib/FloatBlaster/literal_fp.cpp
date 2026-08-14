/********************************************************************
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

#include "stp/FloatBlaster/literal_fp.h"

#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/STPManager/STPManager.h"

#include <cassert>

#include "extlib-constbv/constantbv.h"

namespace stp
{
namespace literal_fp
{

typedef uint32_t bitWidthType;
typedef bitWidthType bwt;
typedef bool proposition;

// The value classes symfpu computes with, over concrete CBV arithmetic.
// This mirrors symfpu's own baseTypes/cvc4_literal.h, with CONSTANTBV as
// the bignum. Everything is by-value with RAII around the heap CBV; these
// live only for the duration of one constant fold.

class roundingMode
{
  unsigned mode;

public:
  roundingMode(unsigned m) : mode(m) {}
  roundingMode(const roundingMode& old) : mode(old.mode) {}
  roundingMode& operator=(const roundingMode& old)
  {
    mode = old.mode;
    return *this;
  }
  proposition operator==(const roundingMode& op) const
  {
    return mode == op.mode;
  }
};

class floatingPointTypeInfo
{
  bitWidthType eb, sb;

public:
  floatingPointTypeInfo(unsigned e, unsigned s) : eb(e), sb(s) {}
  floatingPointTypeInfo(const floatingPointTypeInfo& old)
      : eb(old.eb), sb(old.sb)
  {
  }
  floatingPointTypeInfo& operator=(const floatingPointTypeInfo& old)
  {
    eb = old.eb;
    sb = old.sb;
    return *this;
  }
  bitWidthType exponentWidth(void) const { return eb; }
  bitWidthType significandWidth(void) const { return sb; }
  bitWidthType packedWidth(void) const { return eb + sb; }
  bitWidthType packedExponentWidth(void) const { return eb; }
  bitWidthType packedSignificandWidth(void) const { return sb - 1; }
};

template <bool isSigned> class bitVector;

class traits
{
public:
  typedef bitWidthType bwt;
  typedef roundingMode rm;
  typedef floatingPointTypeInfo fpt;
  typedef proposition prop;
  typedef bitVector<true> sbv;
  typedef bitVector<false> ubv;

  static roundingMode RNE(void)
  {
    return roundingMode(symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  }
  static roundingMode RNA(void)
  {
    return roundingMode(symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY);
  }
  static roundingMode RTP(void)
  {
    return roundingMode(symbolic_fp::ROUND_TOWARD_POSITIVE);
  }
  static roundingMode RTN(void)
  {
    return roundingMode(symbolic_fp::ROUND_TOWARD_NEGATIVE);
  }
  static roundingMode RTZ(void)
  {
    return roundingMode(symbolic_fp::ROUND_TOWARD_ZERO);
  }

  static void precondition(const bool b)
  {
    assert(b);
    (void)b;
  }
  static void postcondition(const bool b)
  {
    assert(b);
    (void)b;
  }
  static void invariant(const bool b)
  {
    assert(b);
    (void)b;
  }
};

template <bool isSigned> class bitVector
{
  bitWidthType width;
  CBV bits; // owned

  friend class bitVector<!isSigned>;

  bitVector(CBV owned_bits, bitWidthType w) : width(w), bits(owned_bits) {}

  static CBV mk(bitWidthType w) { return CONSTANTBV::BitVector_Create(w, true); }

  // Shift amounts arrive as same-width vectors; saturate to the width,
  // which is total and matches what the circuit's shifters produce for
  // oversized amounts (all bits shifted out).
  bitWidthType shiftAmount(const bitVector<isSigned>& op) const
  {
    bitWidthType amount = 0;
    for (bitWidthType i = 0; i < op.width; i++)
      if (CONSTANTBV::BitVector_bit_test(op.bits, i))
      {
        if (i >= 32 || (amount | (1u << i)) >= width)
          return width;
        amount |= (1u << i);
      }
    return amount >= width ? width : amount;
  }

public:
  bitVector(const bwt w, const unsigned v) : width(w), bits(mk(w))
  {
    assert(w > 0);
    for (unsigned i = 0; i < 32 && i < w; i++)
      if (v & (1u << i))
        CONSTANTBV::BitVector_Bit_On(bits, i);
    // The literal must fit; symfpu constructs small constants only.
    assert(w >= 32 || (v >> w) == 0);
  }
  bitVector(const proposition& p) : bitVector(1, p ? 1u : 0u) {}
  bitVector(const bitVector<isSigned>& old)
      : width(old.width), bits(CONSTANTBV::BitVector_Clone(old.bits))
  {
  }
  // Adopt a clone of an existing CBV (used by the driver / conversions).
  static bitVector<isSigned> fromCBV(bitWidthType w, const CBV source)
  {
    assert(bits_(source) == w);
    return bitVector<isSigned>(CONSTANTBV::BitVector_Clone(source), w);
  }
  CBV rawBits() const { return bits; }

  bitVector<isSigned>& operator=(const bitVector<isSigned>& old)
  {
    if (this != &old)
    {
      CONSTANTBV::BitVector_Destroy(bits);
      width = old.width;
      bits = CONSTANTBV::BitVector_Clone(old.bits);
    }
    return *this;
  }
  ~bitVector() { CONSTANTBV::BitVector_Destroy(bits); }

  bwt getWidth(void) const { return width; }

  static bitVector<isSigned> one(const bwt& w) { return bitVector(w, 1); }
  static bitVector<isSigned> zero(const bwt& w) { return bitVector(w, 0); }
  static bitVector<isSigned> allOnes(const bwt& w)
  {
    bitVector<isSigned> r(w, 0);
    CONSTANTBV::BitVector_Fill(r.bits);
    return r;
  }

  proposition isAllOnes() const { return CONSTANTBV::BitVector_is_full(bits); }
  proposition isAllZeros() const { return CONSTANTBV::BitVector_is_empty(bits); }

  static bitVector<isSigned> maxValue(const bwt& w)
  {
    bitVector<isSigned> r(allOnes(w));
    if (isSigned)
      CONSTANTBV::BitVector_Bit_Off(r.bits, w - 1);
    return r;
  }
  static bitVector<isSigned> minValue(const bwt& w)
  {
    bitVector<isSigned> r(w, 0);
    if (isSigned)
      CONSTANTBV::BitVector_Bit_On(r.bits, w - 1);
    return r;
  }

  bitVector<isSigned> operator<<(const bitVector<isSigned>& op) const
  {
    bitVector<isSigned> r(*this);
    CONSTANTBV::BitVector_Move_Left(r.bits, shiftAmount(op));
    return r;
  }
  bitVector<isSigned> operator>>(const bitVector<isSigned>& op) const
  {
    bitVector<isSigned> r(*this);
    const bitWidthType amount = shiftAmount(op);
    CONSTANTBV::BitVector_Move_Right(r.bits, amount);
    if (isSigned && CONSTANTBV::BitVector_msb_(bits))
      for (bitWidthType i = (amount > width) ? 0 : width - amount; i < width;
           i++)
        CONSTANTBV::BitVector_Bit_On(r.bits, i);
    return r;
  }

  bitVector<isSigned> operator|(const bitVector<isSigned>& op) const
  {
    bitVector<isSigned> r(*this);
    CONSTANTBV::Set_Union(r.bits, r.bits, op.bits);
    return r;
  }
  bitVector<isSigned> operator&(const bitVector<isSigned>& op) const
  {
    bitVector<isSigned> r(*this);
    CONSTANTBV::Set_Intersection(r.bits, r.bits, op.bits);
    return r;
  }
  bitVector<isSigned> operator+(const bitVector<isSigned>& op) const
  {
    bitVector<isSigned> r(width, 0);
    CONSTANTBV::boolean carry = false;
    CONSTANTBV::BitVector_add(r.bits, bits, op.bits, &carry);
    return r;
  }
  bitVector<isSigned> operator-(const bitVector<isSigned>& op) const
  {
    bitVector<isSigned> r(width, 0);
    CONSTANTBV::boolean carry = false;
    CONSTANTBV::BitVector_sub(r.bits, bits, op.bits, &carry);
    return r;
  }
  bitVector<isSigned> operator*(const bitVector<isSigned>& op) const
  {
    // Multiply demands room for the full product; compute wide, then take
    // the low half (symfpu widens its operands itself when it needs the
    // exact product, so truncation here matches the circuit).
    const bitWidthType wide = 2 * width;
    CBV a = mk(wide);
    CBV b = mk(wide);
    CONSTANTBV::BitVector_Interval_Copy(a, bits, 0, 0, width);
    CONSTANTBV::BitVector_Interval_Copy(b, op.bits, 0, 0, width);
    if (isSigned)
    {
      if (CONSTANTBV::BitVector_bit_test(bits, width - 1))
        for (bitWidthType i = width; i < wide; i++)
          CONSTANTBV::BitVector_Bit_On(a, i);
      if (CONSTANTBV::BitVector_bit_test(op.bits, width - 1))
        for (bitWidthType i = width; i < wide; i++)
          CONSTANTBV::BitVector_Bit_On(b, i);
    }
    CBV product = mk(wide);
    CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Multiply(product, a, b);
    assert(0 == e);
    (void)e;
    CONSTANTBV::BitVector_Destroy(a);
    CONSTANTBV::BitVector_Destroy(b);
    CBV low = mk(width);
    CONSTANTBV::BitVector_Interval_Copy(low, product, 0, 0, width);
    CONSTANTBV::BitVector_Destroy(product);
    return bitVector<isSigned>(low, width);
  }

  // Total division, SMT-LIB conventions (x/0 = all ones, x%0 = x), the
  // same choices cvc4_literal's *Total operations make. symfpu's uses are
  // guarded so the zero cases should be unreachable; total keeps them
  // defined rather than undefined behaviour if a guard is ever wrong.
  bitVector<isSigned> operator/(const bitVector<isSigned>& op) const
  {
    assert(!isSigned); // symfpu only divides unsigned significands
    if (CONSTANTBV::BitVector_is_empty(op.bits))
      return allOnes(width);
    bitVector<isSigned> quotient(width, 0);
    bitVector<isSigned> remainder(width, 0);
    CBV dividend = CONSTANTBV::BitVector_Clone(bits);
    CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(
        quotient.bits, dividend, op.bits, remainder.bits);
    assert(0 == e);
    (void)e;
    CONSTANTBV::BitVector_Destroy(dividend);
    return quotient;
  }
  bitVector<isSigned> operator%(const bitVector<isSigned>& op) const
  {
    assert(!isSigned);
    if (CONSTANTBV::BitVector_is_empty(op.bits))
      return *this;
    bitVector<isSigned> quotient(width, 0);
    bitVector<isSigned> remainder(width, 0);
    CBV dividend = CONSTANTBV::BitVector_Clone(bits);
    CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(
        quotient.bits, dividend, op.bits, remainder.bits);
    assert(0 == e);
    (void)e;
    CONSTANTBV::BitVector_Destroy(dividend);
    return remainder;
  }

  bitVector<isSigned> operator-(void) const
  {
    bitVector<isSigned> r(width, 0);
    CONSTANTBV::BitVector_Negate(r.bits, bits);
    return r;
  }
  bitVector<isSigned> operator~(void) const
  {
    bitVector<isSigned> r(*this);
    CONSTANTBV::Set_Complement(r.bits, r.bits);
    return r;
  }
  bitVector<isSigned> increment() const
  {
    return *this + bitVector<isSigned>::one(width);
  }
  bitVector<isSigned> decrement() const
  {
    return *this - bitVector<isSigned>::one(width);
  }
  bitVector<isSigned> signExtendRightShift(const bitVector<isSigned>& op) const
  {
    bitVector<isSigned> r(*this);
    const bitWidthType amount = shiftAmount(op);
    CONSTANTBV::BitVector_Move_Right(r.bits, amount);
    if (CONSTANTBV::BitVector_msb_(bits))
      for (bitWidthType i = (amount > width) ? 0 : width - amount; i < width;
           i++)
        CONSTANTBV::BitVector_Bit_On(r.bits, i);
    return r;
  }

  // Modular operations are the plain ones: overflow wraps in CBV exactly
  // as it wraps in the circuit.
  bitVector<isSigned> modularLeftShift(const bitVector<isSigned>& op) const
  {
    return *this << op;
  }
  bitVector<isSigned> modularRightShift(const bitVector<isSigned>& op) const
  {
    return *this >> op;
  }
  bitVector<isSigned> modularIncrement() const { return increment(); }
  bitVector<isSigned> modularDecrement() const { return decrement(); }
  bitVector<isSigned> modularAdd(const bitVector<isSigned>& op) const
  {
    return *this + op;
  }
  bitVector<isSigned> modularSubtract(const bitVector<isSigned>& op) const
  {
    return *this - op;
  }
  bitVector<isSigned> modularNegate() const { return -(*this); }

  proposition operator==(const bitVector<isSigned>& op) const
  {
    return CONSTANTBV::BitVector_equal(bits, op.bits);
  }
  proposition operator<=(const bitVector<isSigned>& op) const
  {
    return compare(op) <= 0;
  }
  proposition operator>=(const bitVector<isSigned>& op) const
  {
    return compare(op) >= 0;
  }
  proposition operator<(const bitVector<isSigned>& op) const
  {
    return compare(op) < 0;
  }
  proposition operator>(const bitVector<isSigned>& op) const
  {
    return compare(op) > 0;
  }

  bitVector<true> toSigned(void) const
  {
    return bitVector<true>(CONSTANTBV::BitVector_Clone(bits), width);
  }
  bitVector<false> toUnsigned(void) const
  {
    return bitVector<false>(CONSTANTBV::BitVector_Clone(bits), width);
  }

  bitVector<isSigned> extend(bwt extension) const
  {
    const bitWidthType w = width + extension;
    CBV out = mk(w);
    if (isSigned && CONSTANTBV::BitVector_msb_(bits))
      CONSTANTBV::BitVector_Fill(out);
    CONSTANTBV::BitVector_Interval_Copy(out, bits, 0, 0, width);
    return bitVector<isSigned>(out, w);
  }
  bitVector<isSigned> contract(bwt reduction) const
  {
    assert(width > reduction);
    const bitWidthType w = width - reduction;
    CBV out = mk(w);
    CONSTANTBV::BitVector_Interval_Copy(out, bits, 0, 0, w);
    return bitVector<isSigned>(out, w);
  }
  bitVector<isSigned> resize(bwt newSize) const
  {
    if (newSize > width)
      return extend(newSize - width);
    if (newSize < width)
      return contract(width - newSize);
    return *this;
  }
  bitVector<isSigned> matchWidth(const bitVector<isSigned>& op) const
  {
    assert(width <= op.width);
    return extend(op.width - width);
  }
  bitVector<isSigned> append(const bitVector<isSigned>& op) const
  {
    // *this becomes the high bits, matching the symbolic backend.
    const bitWidthType w = width + op.width;
    CBV out = mk(w);
    CONSTANTBV::BitVector_Interval_Copy(out, op.bits, 0, 0, op.width);
    CONSTANTBV::BitVector_Interval_Copy(out, bits, op.width, 0, width);
    return bitVector<isSigned>(out, w);
  }
  bitVector<isSigned> extract(bwt upper, bwt lower) const
  {
    assert(upper >= lower);
    const bitWidthType w = upper - lower + 1;
    CBV out = mk(w);
    CONSTANTBV::BitVector_Interval_Copy(out, bits, 0, lower, w);
    return bitVector<isSigned>(out, w);
  }

private:
  int compare(const bitVector<isSigned>& op) const
  {
    assert(width == op.width);
    if (isSigned)
      return CONSTANTBV::BitVector_Compare(bits, op.bits);
    return CONSTANTBV::BitVector_Lexicompare(bits, op.bits);
  }
};

} // namespace literal_fp
} // namespace stp

// symfpu constructs ITEs through this template; over concrete booleans it
// is just selection. The primary template must be visible before the
// specializations.
#include "symfpu/core/ite.h"

namespace symfpu
{
#define STP_LITERAL_ITE(T)                                                     \
  template <> struct ite<stp::literal_fp::proposition, T>                      \
  {                                                                            \
    static T iteOp(const stp::literal_fp::proposition& cond,                   \
                         const T& l, const T& r)                               \
    {                                                                          \
      return cond ? l : r;                                                     \
    }                                                                          \
  };

STP_LITERAL_ITE(stp::literal_fp::traits::rm)
STP_LITERAL_ITE(stp::literal_fp::traits::prop)
STP_LITERAL_ITE(stp::literal_fp::traits::sbv)
STP_LITERAL_ITE(stp::literal_fp::traits::ubv)
#undef STP_LITERAL_ITE
} // namespace symfpu

#include "symfpu/core/add.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/core/unpackedFloat.h"

namespace stp
{
namespace literal_fp
{

typedef symfpu::unpackedFloat<traits> uf;

namespace
{

traits::ubv packedOf(const ASTNode& c)
{
  assert(c.isConstant());
  return traits::ubv::fromCBV(c.GetValueWidth(), c.GetBVConst());
}

floatingPointTypeInfo formatOf(const ASTNode& c)
{
  assert(c.GetExpWidth() != 0);
  return floatingPointTypeInfo(c.GetExpWidth(), c.GetSigWidth());
}

uf unpackChild(const ASTNode& c)
{
  return symfpu::unpack<traits>(formatOf(c), packedOf(c));
}

roundingMode rmOf(const ASTNode& c)
{
  return roundingMode(c.GetUnsignedConst());
}

ASTNode boolResult(STPMgr* bm, bool v)
{
  return v ? bm->ASTTrue : bm->ASTFalse;
}

ASTNode packedResult(STPMgr* bm, const floatingPointTypeInfo& fmt,
                     const uf& value)
{
  const traits::ubv packed(symfpu::pack<traits>(fmt, value));
  return bm->CreateBVConst(CONSTANTBV::BitVector_Clone(packed.rawBits()),
                           fmt.packedWidth());
}

// Whether the node carries a floating-point format at all. Every format the
// parser admits can be evaluated -- the widths symfpu once miscalculated are
// fixed in patches/symfpu/ rather than refused here -- so the format itself
// needs no further check.
bool formatOk(const ASTNode& c)
{
  return c.GetExpWidth() != 0;
}

} // namespace

ASTNode tryEvaluateFpConstant(STPMgr* bm, const ASTNode& n)
{
  const Kind k = n.GetKind();

  switch (k)
  {
    // Binary predicates over same-format operands.
    case FP_LEQ:
    case FP_LT:
    case FP_GEQ:
    case FP_GT:
    case FP_EQ:
    case FP_SMT_EQ:
    {
      if (!formatOk(n[0]) || !formatOk(n[1]))
        return ASTNode();
      const floatingPointTypeInfo fmt = formatOf(n[0]);
      const uf a = unpackChild(n[0]);
      const uf b = unpackChild(n[1]);
      bool v;
      switch (k)
      {
        case FP_LEQ:
          v = symfpu::lessThanOrEqual<traits>(fmt, a, b);
          break;
        case FP_LT:
          v = symfpu::lessThan<traits>(fmt, a, b);
          break;
        case FP_GEQ:
          v = symfpu::lessThanOrEqual<traits>(fmt, b, a);
          break;
        case FP_GT:
          v = symfpu::lessThan<traits>(fmt, b, a);
          break;
        case FP_EQ:
          v = symfpu::ieee754Equal<traits>(fmt, a, b);
          break;
        default:
          v = symfpu::smtlibEqual<traits>(fmt, a, b);
          break;
      }
      return boolResult(bm, v);
    }

    // Unary classifications.
    case FP_ISNORMAL:
    case FP_ISSUBNORMAL:
    case FP_ISZERO:
    case FP_ISINFINITE:
    case FP_ISNAN:
    case FP_ISNEGATIVE:
    case FP_ISPOSITIVE:
    {
      if (!formatOk(n[0]))
        return ASTNode();
      const floatingPointTypeInfo fmt = formatOf(n[0]);
      const uf a = unpackChild(n[0]);
      bool v;
      switch (k)
      {
        case FP_ISNORMAL:
          v = symfpu::isNormal<traits>(fmt, a);
          break;
        case FP_ISSUBNORMAL:
          v = symfpu::isSubnormal<traits>(fmt, a);
          break;
        case FP_ISZERO:
          v = symfpu::isZero<traits>(fmt, a);
          break;
        case FP_ISINFINITE:
          v = symfpu::isInfinite<traits>(fmt, a);
          break;
        case FP_ISNAN:
          v = symfpu::isNaN<traits>(fmt, a);
          break;
        case FP_ISNEGATIVE:
          v = symfpu::isNegative<traits>(fmt, a);
          break;
        default:
          v = symfpu::isPositive<traits>(fmt, a);
          break;
      }
      return boolResult(bm, v);
    }

    case FP_ABS:
    case FP_NEG:
    {
      if (!formatOk(n[0]))
        return ASTNode();
      const floatingPointTypeInfo fmt = formatOf(n[0]);
      const uf a = unpackChild(n[0]);
      return packedResult(bm, fmt,
                          k == FP_ABS ? symfpu::absolute<traits>(fmt, a)
                                      : symfpu::negate<traits>(fmt, a));
    }

    // Rounded binary arithmetic: children are (rm, x, y).
    case FP_ADD:
    case FP_SUB:
    case FP_MUL:
    case FP_DIV:
    {
      if (!formatOk(n[1]) || !formatOk(n[2]))
        return ASTNode();
      const floatingPointTypeInfo fmt = formatOf(n[1]);
      const roundingMode rm = rmOf(n[0]);
      const uf a = unpackChild(n[1]);
      const uf b = unpackChild(n[2]);
      uf r = (k == FP_ADD)   ? symfpu::add<traits>(fmt, rm, a, b, true)
             : (k == FP_SUB) ? symfpu::add<traits>(fmt, rm, a, b, false)
             : (k == FP_MUL) ? symfpu::multiply<traits>(fmt, rm, a, b)
                             : symfpu::divide<traits>(fmt, rm, a, b);
      return packedResult(bm, fmt, r);
    }

    case FP_FMA:
    {
      if (!formatOk(n[1]) || !formatOk(n[2]) || !formatOk(n[3]))
        return ASTNode();
      const floatingPointTypeInfo fmt = formatOf(n[1]);
      const roundingMode rm = rmOf(n[0]);
      const uf x = unpackChild(n[1]);
      const uf y = unpackChild(n[2]);
      const uf z = unpackChild(n[3]);
      return packedResult(bm, fmt, symfpu::fma<traits>(fmt, rm, x, y, z));
    }

    case FP_SQRT:
    {
      if (!formatOk(n[1]))
        return ASTNode();
      const floatingPointTypeInfo fmt = formatOf(n[1]);
      return packedResult(
          bm, fmt, symfpu::sqrt<traits>(fmt, rmOf(n[0]), unpackChild(n[1])));
    }

    case FP_REM:
    {
      if (!formatOk(n[0]) || !formatOk(n[1]))
        return ASTNode();
      const floatingPointTypeInfo fmt = formatOf(n[0]);
      return packedResult(bm, fmt,
                          symfpu::remainder<traits>(fmt, unpackChild(n[0]),
                                                    unpackChild(n[1])));
    }

    case FP_TO_IEEE_BV:
    {
      // The circuit path canonicalises payloads at this boundary; packing
      // the unpacked value does the same (payloads do not survive unpack).
      if (!formatOk(n[0]))
        return ASTNode();
      const floatingPointTypeInfo fmt = formatOf(n[0]);
      return packedResult(bm, fmt, unpackChild(n[0]));
    }

    case FP_TOFP:
    {
      const unsigned eb = n[0].GetUnsignedConst();
      const unsigned sb = n[1].GetUnsignedConst();
      const floatingPointTypeInfo target(eb, sb);
      if (n.Degree() == 3)
      {
        // Reinterpret constant bits.
        if (n[2].GetValueWidth() != eb + sb)
          return ASTNode();
        return packedResult(
            bm, target,
            symfpu::unpack<traits>(target, packedOf(n[2])));
      }
      // (eb, sb, rm, float): round between formats.
      if (n.Degree() != 4 || !formatOk(n[3]))
        return ASTNode();
      return packedResult(bm, target,
                          symfpu::convertFloatToFloat<traits>(
                              formatOf(n[3]), target, rmOf(n[2]),
                              unpackChild(n[3])));
    }

    case FP_TOFP_SIGNED:
    case FP_TOFP_UNSIGNED:
    {
      const unsigned eb = n[0].GetUnsignedConst();
      const unsigned sb = n[1].GetUnsignedConst();
      const floatingPointTypeInfo target(eb, sb);
      const roundingMode rm = rmOf(n[2]);
      const traits::ubv bits = packedOf(n[3]);
      const uf r =
          (k == FP_TOFP_SIGNED)
              ? symfpu::convertSBVToFloat<traits>(target, rm, bits.toSigned())
              : symfpu::convertUBVToFloat<traits>(target, rm, bits);
      return packedResult(bm, target, r);
    }

    // fp.min/fp.max/fp.to_ubv/fp.to_sbv route their unspecified cases
    // through FpTotalise; fp.roundToIntegral keeps the circuit path so its
    // guard-bug refusals stay identical. All fall back.
    default:
      return ASTNode();
  }
}

} // namespace literal_fp
} // namespace stp


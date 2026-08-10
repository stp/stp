/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
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

#include "stp/FloatBlaster/FloatBlast.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/literal_fp.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Util/CBVOps.h"
#include <cassert>

namespace stp
{

// error printing
static void BVConstEvaluatorError(CONSTANTBV::ErrCode e)
{
  std::string ss("BVConstEvaluator:");
  ss += (const char*)BitVector_Error(e);
  FatalError(ss.c_str());
}

// Mirrors ASTNode::GetUnsignedConst.
static unsigned cbvToUnsigned(const CBV v)
{
  if (sizeof(unsigned) * 8 < bits_(v) &&
      CONSTANTBV::Set_Max(v) >= ((signed long)sizeof(unsigned)) * 8)
    FatalError("BVConstEvaluator: constant doesn't fit an unsigned int");
  return *(unsigned*)v;
}

CBV NonMemberBVConstEvaluator(const Kind k, const std::vector<CBV>& args,
                              unsigned outputWidth)
{
  const unsigned width = outputWidth;

  switch (k)
  {
    case BVNOT:
    {
      CBV output = CONSTANTBV::BitVector_Create(width, true);
      CONSTANTBV::Set_Complement(output, args[0]);
      return output;
    }

    case BVSX:
    case BVZX:
    {
      CBV output = CONSTANTBV::BitVector_Create(width, true);
      const unsigned child_width = bits_(args[0]);
      if (width == child_width)
        CONSTANTBV::BitVector_Copy(output, args[0]);
      else
      {
        if (BVSX == k && CONSTANTBV::BitVector_Sign(args[0]) < 0)
          CONSTANTBV::BitVector_Fill(output);
        CONSTANTBV::BitVector_Interval_Copy(output, args[0], 0, 0,
                                            child_width);
      }
      return output;
    }

    case BVLEFTSHIFT:
    case BVRIGHTSHIFT:
    case BVSRSHIFT:
    {
      // The width as a bit-vector, to compare against the amount.
      CBV widthCBV = CONSTANTBV::BitVector_Create(width, true);
      for (unsigned i = 0; i < sizeof(width) * 8; i++)
        if ((width & (1u << i)) != 0)
          CONSTANTBV::BitVector_Bit_On(widthCBV, i);

      CBV output = CONSTANTBV::BitVector_Create(width, true);
      const bool msb = CONSTANTBV::BitVector_msb_(args[0]);

      if (CONSTANTBV::BitVector_Lexicompare(widthCBV, args[1]) < 0)
      {
        // Shifted further than the width.
        if (BVSRSHIFT == k && msb)
          CONSTANTBV::Set_Complement(output, output);
      }
      else
      {
        CONSTANTBV::BitVector_Interval_Copy(output, args[0], 0, 0, width);
        const unsigned shift = cbvToUnsigned(args[1]);
        if (BVLEFTSHIFT == k)
          CONSTANTBV::BitVector_Move_Left(output, shift);
        else
          CONSTANTBV::BitVector_Move_Right(output, shift);

        // A signed shift of an originally negative number.
        if (BVSRSHIFT == k && msb)
          for (unsigned i = 0; i < std::min(shift, width); i++)
            CONSTANTBV::BitVector_Bit_On(output, width - 1 - i);
      }
      CONSTANTBV::BitVector_Destroy(widthCBV);
      return output;
    }

    case BVAND:
    {
      CBV output = allOnes(width);
      for (const CBV a : args)
        CONSTANTBV::Set_Intersection(output, output, a);
      return output;
    }

    case BVOR:
    {
      CBV output = CONSTANTBV::BitVector_Create(width, true);
      for (const CBV a : args)
        CONSTANTBV::Set_Union(output, output, a);
      return output;
    }

    case BVXOR:
    {
      CBV output = CONSTANTBV::BitVector_Create(width, true);
      for (const CBV a : args)
        CONSTANTBV::Set_ExclusiveOr(output, output, a);
      return output;
    }

    case BVSUB:
    {
      CBV output = CONSTANTBV::BitVector_Create(width, true);
      bool carry = false;
      CONSTANTBV::BitVector_sub(output, args[0], args[1], &carry);
      return output;
    }

    case BVUMINUS:
    {
      CBV output = CONSTANTBV::BitVector_Create(width, true);
      CONSTANTBV::BitVector_Negate(output, args[0]);
      return output;
    }

    case BVEXTRACT:
    {
      const unsigned hi = cbvToUnsigned(args[1]);
      const unsigned low = cbvToUnsigned(args[2]);
      const unsigned len = hi - low + 1;
      CBV output = CONSTANTBV::BitVector_Create(len, false);
      CONSTANTBV::BitVector_Interval_Copy(output, args[0], 0, low, len);
      return output;
    }

    case BVCONCAT:
      return CONSTANTBV::BitVector_Concat(args[0], args[1]);

    case BVMULT:
    {
      CBV output = CONSTANTBV::BitVector_Create(width, true);
      CONSTANTBV::BitVector_increment(output); // one.
      CBV tmp = CONSTANTBV::BitVector_Create(2 * width, true);
      for (const CBV a : args)
      {
        CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Multiply(tmp, output, a);
        if (0 != e)
          BVConstEvaluatorError(e);
        CONSTANTBV::BitVector_Interval_Copy(output, tmp, 0, 0, width);
      }
      CONSTANTBV::BitVector_Destroy(tmp);
      return output;
    }

    case BVPLUS:
    {
      CBV output = CONSTANTBV::BitVector_Create(width, true);
      bool carry = false;
      for (const CBV a : args)
      {
        CONSTANTBV::BitVector_add(output, output, a, &carry);
        carry = false;
      }
      return output;
    }

    // SBVREM : Result of rounding the quotient towards
    // zero. i.e. (-10)/3, has a remainder of -1
    //
    // SBVMOD : Result of rounding the quotient towards
    // -infinity. i.e. (-10)/3, has a modulus of 2.  EXCEPT THAT
    // if it divides exactly and the signs are different, then
    // it's equal to the dividend.
    case SBVDIV:
    case SBVREM:
    {
      if (CONSTANTBV::BitVector_is_empty(args[1]))
      {
        // Division by zero, which SMT-LIB defines rather than leaving
        // undefined: (bvsrem s 0) is s, and (bvsdiv s 0) is 1 when s is
        // negative and all ones (that is, -1) when it is not.
        if (SBVREM == k)
          return CONSTANTBV::BitVector_Clone(args[0]);
        if (CONSTANTBV::BitVector_bit_test(args[0], width - 1))
        {
          CBV one = CONSTANTBV::BitVector_Create(width, true);
          CONSTANTBV::BitVector_increment(one);
          return one;
        }
        return allOnes(width);
      }

      CBV quotient = CONSTANTBV::BitVector_Create(width, true);
      CBV remainder = CONSTANTBV::BitVector_Create(width, true);
      CONSTANTBV::ErrCode e =
          CONSTANTBV::BitVector_Divide(quotient, args[0], args[1], remainder);
      if (0 != e)
        BVConstEvaluatorError(e);

      if (SBVDIV == k)
      {
        CONSTANTBV::BitVector_Destroy(remainder);
        return quotient;
      }
      CONSTANTBV::BitVector_Destroy(quotient);
      return remainder;
    }

    case SBVMOD:
    {
      /*
                (bvsmod s t) abbreviates
                    (let ((?msb_s ((_ extract |m-1| |m-1|) s))
                          (?msb_t ((_ extract |m-1| |m-1|) t)))
                      (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
                            (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
                        (let ((u (bvurem abs_s abs_t)))
                          (ite (= u (_ bv0 m))
                               u
                          (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                               u
                          (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                               (bvadd (bvneg u) t)
                          (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                               (bvadd u t)
                               (bvneg u))))))))
      */
      if (CONSTANTBV::BitVector_is_empty(args[1]))
        return CONSTANTBV::BitVector_Clone(args[0]);

      const bool isNegativeS = CONSTANTBV::BitVector_msb_(args[0]);
      const bool isNegativeT = CONSTANTBV::BitVector_msb_(args[1]);

      // Div_Pos destroys its second argument, so operate on copies.
      CBV s = CONSTANTBV::BitVector_Clone(args[0]);
      CBV t = CONSTANTBV::BitVector_Clone(args[1]);
      CBV quotient = CONSTANTBV::BitVector_Create(width, true);
      CBV remainder = CONSTANTBV::BitVector_Create(width, true);
      CBV result = NULL;

      if (!isNegativeS && !isNegativeT)
      {
        CONSTANTBV::ErrCode e =
            CONSTANTBV::BitVector_Div_Pos(quotient, s, t, remainder);
        assert(e == CONSTANTBV::ErrCode_Ok);
        (void)e;
        result = remainder;
        remainder = NULL;
      }
      else if (isNegativeS && !isNegativeT)
      {
        CBV sb = CONSTANTBV::BitVector_Create(width, true);
        CONSTANTBV::BitVector_Negate(sb, s);

        CONSTANTBV::ErrCode e =
            CONSTANTBV::BitVector_Div_Pos(quotient, sb, t, remainder);
        assert(e == CONSTANTBV::ErrCode_Ok);
        (void)e;

        CBV remb = CONSTANTBV::BitVector_Create(width, true);
        CONSTANTBV::BitVector_Negate(remb, remainder);

        result = CONSTANTBV::BitVector_Create(width, true);
        if (!CONSTANTBV::BitVector_is_empty(remb))
        {
          bool carry = false;
          CONSTANTBV::BitVector_add(result, remb, t, &carry);
        }

        CONSTANTBV::BitVector_Destroy(remb);
        CONSTANTBV::BitVector_Destroy(sb);
      }
      else if (!isNegativeS && isNegativeT)
      {
        CBV tb = CONSTANTBV::BitVector_Create(width, true);
        CONSTANTBV::BitVector_Negate(tb, t);

        CONSTANTBV::ErrCode e =
            CONSTANTBV::BitVector_Div_Pos(quotient, s, tb, remainder);
        assert(e == CONSTANTBV::ErrCode_Ok);
        (void)e;

        result = CONSTANTBV::BitVector_Create(width, true);
        if (!CONSTANTBV::BitVector_is_empty(remainder))
        {
          bool carry = false;
          CONSTANTBV::BitVector_add(result, remainder, t, &carry);
        }

        CONSTANTBV::BitVector_Destroy(tb);
      }
      else
      {
        // Signs are both negative.
        CBV sb = CONSTANTBV::BitVector_Create(width, true);
        CBV tb = CONSTANTBV::BitVector_Create(width, true);
        CONSTANTBV::BitVector_Negate(sb, s);
        CONSTANTBV::BitVector_Negate(tb, t);

        CONSTANTBV::ErrCode e =
            CONSTANTBV::BitVector_Div_Pos(quotient, sb, tb, remainder);
        assert(e == CONSTANTBV::ErrCode_Ok);
        (void)e;

        result = CONSTANTBV::BitVector_Create(width, true);
        CONSTANTBV::BitVector_Negate(result, remainder);

        CONSTANTBV::BitVector_Destroy(sb);
        CONSTANTBV::BitVector_Destroy(tb);
      }

      if (remainder != NULL)
        CONSTANTBV::BitVector_Destroy(remainder);
      CONSTANTBV::BitVector_Destroy(quotient);
      CONSTANTBV::BitVector_Destroy(s);
      CONSTANTBV::BitVector_Destroy(t);
      return result;
    }

    case BVDIV:
    case BVMOD:
    {
      if (CONSTANTBV::BitVector_is_empty(args[1]))
      {
        // a = bq + r, where b!=0 implies r < b. q is quotient, r remainder.
        // i.e. a/b = q.
        //
        // Division by zero is defined rather than undefined in SMT-LIB:
        // (bvurem a 0) is a, which follows from the identity above, while
        // (bvudiv a 0) is all ones, which does not. That asymmetry is why
        // the bit-blaster guards BVDIV with an explicit divisor-is-zero
        // test and needs nothing for BVMOD; see the BVDIV case of BBTerm
        // in lib/ToSat/BitBlaster.cpp.
        if (BVMOD == k)
          return CONSTANTBV::BitVector_Clone(args[0]);
        return allOnes(width);
      }

      CBV quotient = CONSTANTBV::BitVector_Create(width, true);
      CBV remainder = CONSTANTBV::BitVector_Create(width, true);

      // Div_Pos destroys its second argument, so pass a copy.
      CBV dividend = CONSTANTBV::BitVector_Clone(args[0]);
      CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(
          quotient, dividend, args[1], remainder);
      CONSTANTBV::BitVector_Destroy(dividend);
      assert(0 == e);
      (void)e;

      if (BVDIV == k)
      {
        CONSTANTBV::BitVector_Destroy(remainder);
        return quotient;
      }
      CONSTANTBV::BitVector_Destroy(quotient);
      return remainder;
    }

    default:
      FatalError("BVConstEvaluator: not a bit-vector term kind");
      return NULL;
  }
}

bool NonMemberBVConstPredicateEvaluator(const Kind k, const CBV a, const CBV b)
{
  switch (k)
  {
    case BOOLEXTRACT:
      return CONSTANTBV::BitVector_bit_test(a, cbvToUnsigned(b));

    case EQ:
      return CONSTANTBV::BitVector_equal(a, b);

    case BVLT:
      return CONSTANTBV::BitVector_Lexicompare(a, b) < 0;
    case BVLE:
      return CONSTANTBV::BitVector_Lexicompare(a, b) <= 0;
    case BVGT:
      return CONSTANTBV::BitVector_Lexicompare(a, b) > 0;
    case BVGE:
      return CONSTANTBV::BitVector_Lexicompare(a, b) >= 0;

    case BVSLT:
      return CONSTANTBV::BitVector_Compare(a, b) < 0;
    case BVSLE:
      return CONSTANTBV::BitVector_Compare(a, b) <= 0;
    case BVSGT:
      return CONSTANTBV::BitVector_Compare(a, b) > 0;
    case BVSGE:
      return CONSTANTBV::BitVector_Compare(a, b) >= 0;

    case BVUADDO:
    {
      const unsigned w = bits_(a);
      CBV sum = CONSTANTBV::BitVector_Create(w, true);
      bool carry = false;
      CONSTANTBV::BitVector_add(sum, a, b, &carry);
      CONSTANTBV::BitVector_Destroy(sum);
      return carry;
    }
    case BVSADDO:
    {
      const unsigned w = bits_(a);
      CBV sum = CONSTANTBV::BitVector_Create(w, true);
      bool carry = false;
      CONSTANTBV::BitVector_add(sum, a, b, &carry);
      // Signed add overflows iff both operands share a sign that differs
      // from the sign of the result.
      const bool s0 = CONSTANTBV::BitVector_msb_(a);
      const bool s1 = CONSTANTBV::BitVector_msb_(b);
      const bool ss = CONSTANTBV::BitVector_msb_(sum);
      CONSTANTBV::BitVector_Destroy(sum);
      return (s0 == s1) && (s0 != ss);
    }
    case BVUMULO:
    case BVSMULO:
    {
      const unsigned w = bits_(a);
      const bool isSigned = (k == BVSMULO);
      // Extend both operands (zero- or sign-extend), multiply exactly, then
      // inspect the high bits. BitVector_Multiply is a signed multiply that
      // reports overflow once the product's magnitude reaches the
      // destination's sign bit, so the intermediates need 2w+1 bits: an
      // unsigned product can be up to (2^w-1)^2, which exceeds the signed
      // 2w-bit maximum but fits in 2w+1 bits.
      const unsigned ew = 2 * w + 1;
      CBV y2 = CONSTANTBV::BitVector_Create(ew, true);
      CBV z2 = CONSTANTBV::BitVector_Create(ew, true);
      CBV prod = CONSTANTBV::BitVector_Create(ew, true);
      if (isSigned && CONSTANTBV::BitVector_Sign(a) < 0)
        CONSTANTBV::BitVector_Fill(y2);
      if (isSigned && CONSTANTBV::BitVector_Sign(b) < 0)
        CONSTANTBV::BitVector_Fill(z2);
      CONSTANTBV::BitVector_Interval_Copy(y2, a, 0, 0, w);
      CONSTANTBV::BitVector_Interval_Copy(z2, b, 0, 0, w);
      CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Multiply(prod, y2, z2);
      if (0 != e)
        BVConstEvaluatorError(e);
      bool overflow = false;
      if (isSigned)
      {
        // Overflow iff the product is not the sign-extension of its low w
        // bits.
        const bool sign = CONSTANTBV::BitVector_bit_test(prod, w - 1);
        for (unsigned i = w; i < ew; i++)
          if (CONSTANTBV::BitVector_bit_test(prod, i) != sign)
            overflow = true;
      }
      else
      {
        // Overflow iff any high bit is set.
        for (unsigned i = w; i < ew; i++)
          if (CONSTANTBV::BitVector_bit_test(prod, i))
            overflow = true;
      }
      CONSTANTBV::BitVector_Destroy(y2);
      CONSTANTBV::BitVector_Destroy(z2);
      CONSTANTBV::BitVector_Destroy(prod);
      return overflow;
    }
    case BVUSUBO:
      // Unsigned subtraction overflows (borrows) iff a <u b.
      return CONSTANTBV::BitVector_Lexicompare(a, b) < 0;
    case BVSSUBO:
    {
      const unsigned w = bits_(a);
      CBV diff = CONSTANTBV::BitVector_Create(w, true);
      bool carry = false;
      // diff = a - b
      CONSTANTBV::BitVector_sub(diff, a, b, &carry);
      // Signed subtraction overflows iff the operands differ in sign and the
      // result's sign differs from the minuend's sign.
      const bool s0 = CONSTANTBV::BitVector_msb_(a);
      const bool s1 = CONSTANTBV::BitVector_msb_(b);
      const bool sd = CONSTANTBV::BitVector_msb_(diff);
      CONSTANTBV::BitVector_Destroy(diff);
      return (s0 != s1) && (s0 != sd);
    }

    default:
      FatalError("BVConstEvaluator: not a two-argument predicate kind");
      return false;
  }
}

static int64_t toSigned64(uint64_t v, unsigned width)
{
  if (width >= 64)
    return (int64_t)v;
  if ((v >> (width - 1)) & 1)
    return (int64_t)(v | ~mask64(width));
  return (int64_t)v;
}

uint64_t NonMemberBVConstEvaluator64(const Kind k,
                                     const std::vector<uint64_t>& args,
                                     const std::vector<unsigned>& argWidths,
                                     unsigned outputWidth)
{
  const unsigned width = outputWidth;
  const uint64_t m = mask64(width);
  const uint64_t x = args[0];
  const uint64_t y = args.size() > 1 ? args[1] : 0;

  switch (k)
  {
    case BVNOT:
      return ~x & m;

    case BVUMINUS:
      return (0 - x) & m;

    case BVSX:
      return (uint64_t)toSigned64(x, argWidths[0]) & m;

    case BVZX:
      return x;

    // Shifting by the width or more pushes everything out; an arithmetic
    // shift then leaves the sign bit everywhere.
    case BVLEFTSHIFT:
      return y >= width ? 0 : (x << y) & m;
    case BVRIGHTSHIFT:
      return y >= width ? 0 : x >> y;
    case BVSRSHIFT:
    {
      const int64_t sx = toSigned64(x, width);
      if (y >= width)
        return sx < 0 ? m : 0;
      return (uint64_t)(sx >> y) & m;
    }

    case BVAND:
    {
      uint64_t r = m;
      for (const uint64_t a : args)
        r &= a;
      return r;
    }

    case BVOR:
    {
      uint64_t r = 0;
      for (const uint64_t a : args)
        r |= a;
      return r;
    }

    case BVXOR:
    {
      uint64_t r = 0;
      for (const uint64_t a : args)
        r ^= a;
      return r;
    }

    case BVSUB:
      return (x - y) & m;

    case BVEXTRACT:
    {
      const uint64_t hi = args[1];
      const uint64_t low = args[2];
      return (x >> low) & mask64((unsigned)(hi - low + 1));
    }

    case BVCONCAT:
      return (x << argWidths[1]) | y;

    case BVMULT:
    {
      uint64_t r = 1;
      for (const uint64_t a : args)
        r = (r * a) & m;
      return r;
    }

    case BVPLUS:
    {
      uint64_t r = 0;
      for (const uint64_t a : args)
        r += a;
      return r & m;
    }

    // Division by zero is defined in SMT-LIB; see the CBV evaluator above
    // for the details.
    case BVDIV:
      return y == 0 ? m : x / y;
    case BVMOD:
      return y == 0 ? x : x % y;

    case SBVDIV:
    {
      const int64_t sx = toSigned64(x, width);
      const int64_t sy = toSigned64(y, width);
      if (sy == 0)
        return sx < 0 ? 1 : m;
      // The lone overflow, INT64_MIN / -1, wraps back to INT64_MIN.
      if (sx == INT64_MIN && sy == -1)
        return x;
      return (uint64_t)(sx / sy) & m;
    }

    case SBVREM:
    {
      const int64_t sx = toSigned64(x, width);
      const int64_t sy = toSigned64(y, width);
      if (sy == 0)
        return x;
      if (sy == -1) // INT64_MIN % -1 overflows; the remainder is 0 anyway.
        return 0;
      return (uint64_t)(sx % sy) & m;
    }

    case SBVMOD:
    {
      // Truncated remainder, then pulled onto the divisor's side of zero:
      // the result is either zero or has the divisor's sign.
      const int64_t sx = toSigned64(x, width);
      const int64_t sy = toSigned64(y, width);
      if (sy == 0)
        return x;
      if (sy == -1)
        return 0;
      int64_t r = sx % sy;
      if (r != 0 && (r < 0) != (sy < 0))
        r += sy;
      return (uint64_t)r & m;
    }

    default:
      FatalError("BVConstEvaluator64: not a bit-vector term kind");
      return 0;
  }
}

bool NonMemberBVConstPredicateEvaluator64(const Kind k, const uint64_t a,
                                          const uint64_t b,
                                          const unsigned width)
{
  switch (k)
  {
    case BOOLEXTRACT:
      return (a >> b) & 1;

    case EQ:
      return a == b;

    case BVLT:
      return a < b;
    case BVLE:
      return a <= b;
    case BVGT:
      return a > b;
    case BVGE:
      return a >= b;

    case BVSLT:
      return toSigned64(a, width) < toSigned64(b, width);
    case BVSLE:
      return toSigned64(a, width) <= toSigned64(b, width);
    case BVSGT:
      return toSigned64(a, width) > toSigned64(b, width);
    case BVSGE:
      return toSigned64(a, width) >= toSigned64(b, width);

    default:
      FatalError("BVConstEvaluator64: not a two-argument predicate kind");
      return false;
  }
}

// Const evaluator logical and arithmetic operations.
ASTNode NonMemberBVConstEvaluator(STPMgr* _bm, const Kind k,
                                  const ASTVec& input_children,
                                  unsigned int inputwidth)
{
  ASTNode OutputNode;

  ASTNode& ASTTrue = _bm->ASTTrue;
  ASTNode& ASTFalse = _bm->ASTFalse;

  const size_t number_of_children = input_children.size();
  assert(number_of_children >= 1);
  assert(k != BVCONST);

  ASTVec children;
  children.reserve(number_of_children);
  for (size_t i = 0; i < number_of_children; i++)
  {
    if (input_children[i].isConstant())
      children.push_back(input_children[i]);
    else
      children.push_back(NonMemberBVConstEvaluator(_bm, input_children[i]));
  }

  switch (k)
  {
    case UNDEFINED:
    case READ:
    case WRITE:
    case SYMBOL:
      FatalError("BVConstEvaluator: term is not a constant-term");
      break;
    // case BVCONST:
    //        OutputNode = t;
    //      break;

    // The bit-vector terms, evaluated straight on the bit-vectors.
    case BVNOT:
    case BVSX:
    case BVZX:
    case BVLEFTSHIFT:
    case BVRIGHTSHIFT:
    case BVSRSHIFT:
    case BVAND:
    case BVOR:
    case BVXOR:
    case BVSUB:
    case BVUMINUS:
    case BVEXTRACT:
    case BVCONCAT:
    case BVMULT:
    case BVPLUS:
    case SBVDIV:
    case SBVREM:
    case SBVMOD:
    case BVDIV:
    case BVMOD:
    {
      std::vector<CBV> args;
      args.reserve(number_of_children);
      for (const ASTNode& c : children)
        args.push_back(c.GetBVConst());

      const CBV output = NonMemberBVConstEvaluator(k, args, inputwidth);
      OutputNode = _bm->CreateBVConst(output, bits_(output));
      break;
    }

    // The predicates over two bit-vectors.
    case BOOLEXTRACT:
    case EQ:
    case BVLT:
    case BVLE:
    case BVGT:
    case BVGE:
    case BVSLT:
    case BVSLE:
    case BVSGT:
    case BVSGE:
    case BVUADDO:
    case BVSADDO:
    case BVUMULO:
    case BVSMULO:
    case BVUSUBO:
    case BVSSUBO:
      assert(2 == number_of_children);
      OutputNode = NonMemberBVConstPredicateEvaluator(
                       k, children[0].GetBVConst(), children[1].GetBVConst())
                       ? ASTTrue
                       : ASTFalse;
      break;

    case ITE:
    {
      // As with NOT: the condition must be read after eager folding.
      if (ASTTrue == children[0])
        OutputNode = children[1];
      else if (ASTFalse == children[0])
        OutputNode = children[2];
      else
      {
        std::cerr << children[0];
        FatalError(
            "BVConstEvaluator: ITE condiional must be either TRUE or FALSE:");
      }
    }
    break;

    case TRUE:
      OutputNode = ASTTrue;
      break;
    case FALSE:
      OutputNode = ASTFalse;
      break;
    case NOT:
      // Test the eagerly-folded child, like every other case: the raw
      // input child may be an unsimplified formula that folds to a
      // constant (e.g. when the caller built the tree with a
      // non-simplifying factory).
      if (ASTTrue == children[0])
        return ASTFalse;
      else if (ASTFalse == children[0])
        return ASTTrue;
      else
      {
        std::cerr << children[0];
        FatalError("BVConstEvaluator: unexpected not input");
      }

    case OR:
      OutputNode = ASTFalse;
      for (ASTVec::const_iterator it = children.begin(), itend = children.end();
           it != itend; it++)
        if (ASTTrue == *it)
          OutputNode = ASTTrue;

      break;

    case NOR:
    {
      ASTNode o = ASTFalse;
      for (ASTVec::const_iterator it = children.begin(), itend = children.end();
           it != itend; it++)
      {
        if (ASTTrue == (*it))
        {
          o = ASTTrue;
          break;
        }
      }

      if (o == ASTTrue)
        OutputNode = ASTFalse;
      else
        OutputNode = ASTTrue;

      break;
    }

    case XOR:
    {
      bool output = false;
      for (ASTVec::const_iterator it = children.begin(), itend = children.end();
           it != itend; it++)
      {
        if (ASTTrue == *it)
          output = !output; // parity.
      }

      if (output)
        OutputNode = ASTTrue;
      else
        OutputNode = ASTFalse;

      break;
    }

    case AND:
    {
      OutputNode = ASTTrue;
      for (ASTVec::const_iterator it = children.begin(), itend = children.end();
           it != itend; it++)
      {
        if (ASTFalse == (*it))
        {
          OutputNode = ASTFalse;
          break;
        }
      }
      break;
    }

    case NAND:
    {
      OutputNode = ASTFalse;
      for (ASTVec::const_iterator it = children.begin(), itend = children.end();
           it != itend; it++)
      {
        if (ASTFalse == (*it))
        {
          OutputNode = ASTTrue;
          break;
        }
      }
      break;
    }

    case IFF:
    {
      assert(2 == number_of_children);
      const ASTNode& t0 = children[0];
      const ASTNode& t1 = children[1];
      if ((ASTTrue == t0 && ASTTrue == t1) ||
          (ASTFalse == t0 && ASTFalse == t1))
        OutputNode = ASTTrue;
      else
        OutputNode = ASTFalse;
      break;
    }

    case IMPLIES:
    {
      assert(2 == number_of_children);
      const ASTNode& t0 = children[0];
      const ASTNode& t1 = children[1];
      if ((ASTFalse == t0) || (ASTTrue == t0 && ASTTrue == t1))
        OutputNode = ASTTrue;
      else
        OutputNode = ASTFalse;
      break;
    }
    case FP_LEQ:
    case FP_LT:
    case FP_GEQ:
    case FP_GT:
    case FP_EQ:
    case FP_ISNORMAL:
    case FP_ISSUBNORMAL:
    case FP_ISZERO:
    case FP_ISINFINITE:
    case FP_ISNAN:
    case FP_ISNEGATIVE:
    case FP_ISPOSITIVE:
    case FP_ABS:
    case FP_NEG:
    case FP_ADD:
    case FP_SUB:
    case FP_MUL:
    case FP_DIV:
    case FP_FMA:
    case FP_SQRT:
    case FP_REM:
    case FP_ROUNDTOINTEGRAL:
    case FP_MIN:
    case FP_MAX:
    case FP_TOFP:
    case FP_TOFP_SIGNED:
    case FP_TOFP_UNSIGNED:
    case FP_TO_UBV:
    case FP_TO_SBV:
    case FP_TO_IEEE_BV:
    case FP_SMT_EQ:
    {
      // A float's format is carried on the node, not implied by its kind, so
      // it is lost every time a node is rebuilt -- and evaluating a nested
      // operation rebuilds one. The inner operation's result comes back from
      // NonMemberBVConstEvaluator as a bare BVCONST with no format, and the
      // outer operation then blasts it against a format of (0, 0). That does
      // not fail; it computes the wrong bits. Recover the format from
      // whichever child still has one and put it back on the others.
      unsigned int exp_width = 0;
      unsigned int sig_width = 0;

      if (k == FP_TOFP || k == FP_TOFP_SIGNED || k == FP_TOFP_UNSIGNED)
      {
        // to_fp names its target format in its first two children rather
        // than inheriting it from an operand.
        assert(children.size() >= 2);
        exp_width = children[0].GetUnsignedConst();
        sig_width = children[1].GetUnsignedConst();
      }
      else
      {
        for (size_t i = 0; i < children.size(); i++)
        {
          if (children[i].GetExpWidth() != 0)
          {
            exp_width = children[i].GetExpWidth();
            sig_width = children[i].GetSigWidth();
            break;
          }
        }
      }

      ASTVec formatted;
      formatted.reserve(children.size());

      // to_fp's operands are not floats to be re-formatted: children 0 and 1
      // are the target format, and the source is either a float that already
      // carries its own format or a bitvector that must stay one. Stamping a
      // format onto that source would make a 32-bit integer argument look
      // like a Float32 and take the reformat path instead of the convert one.
      const bool format_children =
          (k != FP_TOFP && k != FP_TOFP_SIGNED && k != FP_TOFP_UNSIGNED &&
           k != FP_TO_UBV && k != FP_TO_SBV);

      // fp.to_ubv/fp.to_sbv are the same story from the other side: their
      // children are (m, rm, x, unspecified), of which only x is a float, and
      // their *result* is a bitvector. Both the width argument and the result
      // happen to be as wide as e + s in the common 32-bit case, so stamping
      // a format on them would turn an integer into a Float32.

      for (size_t i = 0; i < children.size(); i++)
      {
        if (!format_children)
        {
          formatted.push_back(children[i]);
          continue;
        }

        // Rounding modes and to_fp's format arguments are bitvectors that
        // are not floats; leave them alone. A float operand is as wide as
        // the format it is packed in.
        //
        // A plain BVCONST cannot carry a format at all -- ASTBVConst's
        // getExpWidth() is hardwired to 0 and its setter asserts -- so the
        // constant has to be re-made as an ASTFPConst first. That is what
        // CreateFPConst is for, and what the lowering pass does with its
        // own result.
        formatted.push_back(
            FloatBlaster::withFormat(_bm, children[i], exp_width, sig_width));
      }

      // The predicates are formulas; everything else is a term of the node's
      // own width (which for to_ubv/to_sbv is the target width, not
      // exp + sig). CreateNode would leave a term's value width zero.
      const bool boolean_result =
          k == FP_LEQ || k == FP_LT || k == FP_GEQ || k == FP_GT ||
          k == FP_EQ || k == FP_SMT_EQ || k == FP_ISNORMAL ||
          k == FP_ISSUBNORMAL || k == FP_ISZERO || k == FP_ISINFINITE ||
          k == FP_ISNAN || k == FP_ISNEGATIVE || k == FP_ISPOSITIVE;

      // Build the normalisation copy through the HASHING factory, never the
      // default one: the simplifying factory folds all-constant
      // floating-point nodes by calling back into this evaluator, so
      // rebuilding the same kind over the same constant children through it
      // would recurse without bound. Nothing is lost -- the factory
      // shortcuts this skips (abs of a constant, x*1.0, same-operand
      // comparisons) are all handled by lowering below, and the evaluation
      // of `blasted` already supports an unfolded circuit.
      ASTNode temp(boolean_result
                       ? _bm->hashingNodeFactory->CreateNode(k, formatted)
                       : _bm->hashingNodeFactory->CreateTerm(k, inputwidth,
                                                             formatted));

      // Only a floating-point *result* carries a floating-point format. The
      // classifications and comparisons return a Boolean and to_ubv/to_sbv
      // return a bit-vector; stamping a format on temp for those is wrong,
      // because lowering would then copy temp's format onto its output --
      // poisoning the shared Boolean constant, whose GetType() afterwards reads
      // FLOATINGPOINT and sends the constant evaluator down its bit-vector
      // (GetBVConst) path. temp's type already distinguishes the cases.
      const bool float_result = (temp.GetType() == FLOATINGPOINT_TYPE);
      if (float_result)
      {
        temp.SetExpWidth(exp_width);
        temp.SetSigWidth(sig_width);
      }

      // The factory may have rewritten the operation as it was built:
      // folded it to a constant (abs/neg of a constant is a sign-bit edit,
      // x*1.0 folds to x), or into different structure entirely -- fp.leq of
      // a term with itself becomes (not (fp.isNaN ...)). Interned constants
      // compare pointer-equal, so the same-operand rules do fire here. In
      // either case evaluate what came back rather than blasting it: the
      // blaster only handles floating-point operations, and asserts on
      // anything else.
      if (temp.GetKind() != k)
      {
        OutputNode =
            temp.isConstant() ? temp : NonMemberBVConstEvaluator(_bm, temp);
        if (float_result)
          OutputNode =
              FloatBlaster::withFormat(_bm, OutputNode, exp_width, sig_width);
        break;
      }

      // Evaluate directly when the literal backend covers the operation:
      // the same symfpu semantics as the circuit, instantiated over
      // concrete CBV arithmetic -- microseconds instead of building and
      // collapsing thousands of interned gates. The per-kind agreement of
      // the two paths is machine-checked exhaustively at a small format
      // (FpConstantFold_Test) and against the hardware oracle.
      {
        const ASTNode literal = literal_fp::tryEvaluateFpConstant(_bm, temp);
        if (!literal.IsNull())
        {
          OutputNode = literal;
          if (float_result)
            OutputNode =
                FloatBlaster::withFormat(_bm, OutputNode, exp_width, sig_width);
          break;
        }
      }

      // One table, the same one the solver's lowering pass uses, reached with
      // the node rather than with its parts: it reads each operand's format
      // from its source sort, so nothing here has to work out which child
      // carries the format and pass it alongside.
      ASTNode blasted(FloatBlast::lowerOperation(_bm, temp));

      // How much work the next line is depends on the installed factory: a
      // simplifying one has already folded the circuit to its answer while
      // building it, so this is a no-op; a hashing one hands back the circuit
      // itself, and it is evaluated here. Both are supported, which is what
      // the memo in NonMemberBVConstEvaluator is for -- the circuit is a
      // deeply shared DAG, and evaluating it by paths does not finish.
      OutputNode = NonMemberBVConstEvaluator(_bm, blasted);

      // Carry the format out, so an enclosing operation sees a formatted
      // operand rather than a bare bit-vector.
      if (float_result)
        OutputNode =
            FloatBlaster::withFormat(_bm, OutputNode, exp_width, sig_width);
      break;
    }
    default:
      FatalError("BVConstEvaluator: The input kind is not supported yet:");
      break;
  }
  /*
    if(BVCONST != k){
    cerr<<inputwidth<<endl;
    cerr<<"------------------------"<<endl;
    t.LispPrint(cerr);
    cerr<<endl;
    OutputNode.LispPrint(cerr);
    cerr<<endl<<"------------------------"<<endl;
    }
  */
  assert(OutputNode.isConstant());
  // UpdateSimplifyMap(t,OutputNode,false);
  return OutputNode;
}

// One evaluation per distinct node, rather than one per path to it.
//
// The argument is a DAG and the walk below is a tree walk, so without this a
// shared subterm is re-evaluated once for every route into it. That is
// affordable for the word-level bit-vector nodes this was written for, whose
// sharing is shallow. It is not affordable for a lowered floating-point
// circuit: those are deeply shared by construction, and the floating-point
// arm above folds by lowering the operation and then evaluating the circuit
// it gets back. A single Float(3,4) fp.add does not finish.
//
// It has not bitten because the CLI and the C API both install the
// simplifying factory, which folds as it builds -- so lowerOperation hands
// back a BVCONST that is already the answer and the evaluation below is a
// no-op. That is a property of the caller's configuration, not of this
// module, and STPMgr's own constructor installs the hashing factory instead.
//
// Children are evaluated here rather than left to the kind-and-children
// overload, which does the same thing one level down but has no memo to
// consult. Handing it constants throughout makes its own recursion
// unreachable; the two agree on everything else, since it evaluates every
// child eagerly regardless of kind.
static ASTNode evaluateMemoised(STPMgr* mgr, const ASTNode& t,
                                ASTNodeMap& memo)
{
  if (t.isConstant())
    return t;

  const ASTNodeMap::const_iterator cached = memo.find(t);
  if (cached != memo.end())
    return cached->second;

  ASTVec children;
  children.reserve(t.Degree());
  for (size_t i = 0; i < t.Degree(); i++)
    children.push_back(evaluateMemoised(mgr, t[i], memo));

  const ASTNode out = NonMemberBVConstEvaluator(mgr, t.GetKind(), children,
                                                t.GetValueWidth());
  memo[t] = out;
  return out;
}

// Const evaluator logical and arithmetic operations.
ASTNode NonMemberBVConstEvaluator(STPMgr* mgr, const ASTNode& t)
{
  if (t.isConstant())
    return t;

  // The common case by far: an operation over constants, reached from the
  // simplifying factory's fold. There is nothing under it to share, so it
  // does not pay for a memo it would use once.
  bool children_are_constant = true;
  for (size_t i = 0; i < t.Degree(); i++)
    if (!t[i].isConstant())
    {
      children_are_constant = false;
      break;
    }

  if (children_are_constant)
    return NonMemberBVConstEvaluator(mgr, t.GetKind(),
                                     toASTVec(t.GetChildren()),
                                     t.GetValueWidth());

  ASTNodeMap memo;
  return evaluateMemoised(mgr, t, memo);
}

} // end of namespace stp

/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2026
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

#include "stp/Simplifier/ValueSetAnalysis.h"
#include "stp/Simplifier/Simplifier.h"

namespace stp
{

  const size_t ValueSet::MAX_ELEMENTS;

  ValueSet* ValueSetAnalysis::fresh(const ASTNode& n) const
  {
    return new ValueSet(n.GetValueWidth() > 0 ? n.GetValueWidth() : 1,
                        BOOLEAN_TYPE == n.GetType());
  }

  namespace
  {
    CBV valueOf(unsigned width, uint64_t value)
    {
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      for (unsigned i = 0; i < width && i < 64; i++)
        if ((value >> i) & 1)
          CONSTANTBV::BitVector_Bit_On(result, i);
      return result;
    }

    CBV allOnes(unsigned width)
    {
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      CONSTANTBV::BitVector_Fill(result);
      return result;
    }

    // The shift amount, saturated at the width: shifting by the width or
    // more always gives the same answer.
    unsigned shiftAmount(const CBV v, unsigned width)
    {
      uint64_t result = 0;
      for (unsigned i = 0; i < bits_(v); i++)
        if (CONSTANTBV::BitVector_bit_test(v, i))
        {
          if (i >= 63)
            return width;
          result |= (1ull << i);
          if (result >= width)
            return width;
        }
      return (unsigned)result;
    }

    CBV boolCBV(bool b)
    {
      CBV r = CONSTANTBV::BitVector_Create(1, true);
      if (b)
        CONSTANTBV::BitVector_Bit_On(r, 0);
      return r;
    }

    bool isTrue(const CBV v) { return CONSTANTBV::BitVector_bit_test(v, 0); }

    // Mirrors ASTNode::GetUnsignedConst.
    unsigned toUnsigned(const CBV v)
    {
      if (sizeof(unsigned) * 8 < bits_(v) &&
          CONSTANTBV::Set_Max(v) >= ((signed long)sizeof(unsigned)) * 8)
        FatalError("ValueSetAnalysis: constant doesn't fit an unsigned int");
      return *(unsigned*)v;
    }

    // What NonMemberBVConstEvaluator (consteval.cpp) computes, case for
    // case, but straight on the bit-vectors: building a hash-consed
    // constant node for every child member and every result is most of
    // what the analysis used to spend its time on. Booleans are width-1
    // vectors with bit zero as the truth value. Returns a fresh CBV the
    // caller owns.
    CBV evalOnCBVs(Kind k, const ASTNode& n, const vector<CBV>& args)
    {
      const unsigned width = n.GetValueWidth(); // 0 for the boolean kinds.

      switch (k)
      {
        case BOOLEXTRACT:
          return boolCBV(
              CONSTANTBV::BitVector_bit_test(args[0], toUnsigned(args[1])));

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
          const unsigned child_width = n[0].GetValueWidth();
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
            const unsigned shift = toUnsigned(args[1]);
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
          const unsigned low = toUnsigned(args[2]);
          assert(width == toUnsigned(args[1]) - low + 1);
          CBV output = CONSTANTBV::BitVector_Create(width, false);
          CONSTANTBV::BitVector_Interval_Copy(output, args[0], 0, low, width);
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
            CONSTANTBV::ErrCode e =
                CONSTANTBV::BitVector_Multiply(tmp, output, a);
            if (0 != e)
              FatalError((const char*)CONSTANTBV::BitVector_Error(e));
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

        case SBVDIV:
        case SBVREM:
        {
          if (CONSTANTBV::BitVector_is_empty(args[1]))
          {
            // Division by zero, which SMT-LIB defines: (bvsrem s 0) is s,
            // and (bvsdiv s 0) is 1 when s is negative and all ones (that
            // is, -1) when it is not.
            if (SBVREM == k)
              return CONSTANTBV::BitVector_Clone(args[0]);
            if (CONSTANTBV::BitVector_bit_test(args[0], width - 1))
              return valueOf(width, 1);
            return allOnes(width);
          }

          CBV quotient = CONSTANTBV::BitVector_Create(width, true);
          CBV remainder = CONSTANTBV::BitVector_Create(width, true);
          CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Divide(
              quotient, args[0], args[1], remainder);
          if (0 != e)
            FatalError((const char*)CONSTANTBV::BitVector_Error(e));

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
          // See the SBVMOD case of consteval.cpp for the SMT-LIB
          // definition this follows.
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
            // (bvurem a 0) is a and (bvudiv a 0) is all ones; see the
            // BVDIV case of consteval.cpp for why.
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

        case EQ:
          return boolCBV(CONSTANTBV::BitVector_equal(args[0], args[1]));

        case BVLT:
          return boolCBV(
              CONSTANTBV::BitVector_Lexicompare(args[0], args[1]) < 0);
        case BVLE:
          return boolCBV(
              CONSTANTBV::BitVector_Lexicompare(args[0], args[1]) <= 0);
        case BVGT:
          return boolCBV(
              CONSTANTBV::BitVector_Lexicompare(args[0], args[1]) > 0);
        case BVGE:
          return boolCBV(
              CONSTANTBV::BitVector_Lexicompare(args[0], args[1]) >= 0);

        case BVSLT:
          return boolCBV(CONSTANTBV::BitVector_Compare(args[0], args[1]) < 0);
        case BVSLE:
          return boolCBV(CONSTANTBV::BitVector_Compare(args[0], args[1]) <= 0);
        case BVSGT:
          return boolCBV(CONSTANTBV::BitVector_Compare(args[0], args[1]) > 0);
        case BVSGE:
          return boolCBV(CONSTANTBV::BitVector_Compare(args[0], args[1]) >= 0);

        case NOT:
          return boolCBV(!isTrue(args[0]));

        case OR:
        case NOR:
        {
          bool any = false;
          for (const CBV a : args)
            if (isTrue(a))
            {
              any = true;
              break;
            }
          return boolCBV(OR == k ? any : !any);
        }

        case AND:
        case NAND:
        {
          bool all = true;
          for (const CBV a : args)
            if (!isTrue(a))
            {
              all = false;
              break;
            }
          return boolCBV(AND == k ? all : !all);
        }

        case XOR:
        {
          bool parity = false;
          for (const CBV a : args)
            if (isTrue(a))
              parity = !parity;
          return boolCBV(parity);
        }

        case IFF:
          return boolCBV(isTrue(args[0]) == isTrue(args[1]));

        case IMPLIES:
          return boolCBV(!isTrue(args[0]) || isTrue(args[1]));

        default:
          // ITE is handled before evaluation is reached; nothing else
          // passes constEvaluable.
          FatalError("ValueSetAnalysis: unexpected kind");
          return NULL;
      }
    }

    // Operations that are one-to-one in each argument (or, for equality,
    // reach both answers whatever the other side is): once an operand is
    // unknown the result can be anything, so there is nothing to say.
    bool anythingWhenUnknown(Kind k)
    {
      switch (k)
      {
        case EQ:
        case IFF:
        case XOR:
        case NOT:
        case BVXOR:
        case BVNOT:
        case BVPLUS:
        case BVSUB:
        case BVUMINUS:
          return true;
        default:
          return false;
      }
    }
  }

  bool ValueSetAnalysis::constEvaluable(Kind k)
  {
    // The kinds the switch in NonMemberBVConstEvaluator handles; it
    // exits fatally on anything else. Note BVNAND/BVNOR/BVXNOR are not
    // implemented there.
    switch (k)
    {
      case BOOLEXTRACT:
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
      case ITE:
      case EQ:
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
      case BVSLT:
      case BVSLE:
      case BVSGT:
      case BVSGE:
      case NOT:
      case OR:
      case NOR:
      case XOR:
      case AND:
      case NAND:
      case IFF:
      case IMPLIES:
        return true;
      default:
        return false;
    }
  }

  // An unknown child stands for every value of its width. Rather than give
  // up, list values that produce exactly the same results -- there are
  // usually few or none of them, and the caller stops as soon as too many
  // results pile up.
  bool ValueSetAnalysis::standIns(const ASTNode& n, size_t index,
                                  const vector<const ValueSet*>& children,
                                  vector<CBV>& out, Expand& expandWith)
  {
    const Kind k = n.GetKind();
    const unsigned width = std::max(1u, n[index].GetValueWidth());

    if (anythingWhenUnknown(k))
      return false;

    switch (k)
    {
      // Multiplication, division and modulus are left out on purpose:
      // they are the expensive ones to evaluate, and an unknown operand
      // rarely pins their result down.
      case BVMULT:
      case BVDIV:
      case BVMOD:
      case SBVDIV:
      case SBVREM:
      case SBVMOD:
        return false;

      case BVAND:
        expandWith = Expand::Submask;
        out.push_back(allOnes(width));
        return true;

      case BVOR:
        expandWith = Expand::Supermask;
        out.push_back(CONSTANTBV::BitVector_Create(width, true));
        return true;

      // The comparisons are monotone in each side, so whatever they can
      // answer they already answer at the extremes of the unknown one.
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
        out.push_back(CONSTANTBV::BitVector_Create(width, true));
        out.push_back(allOnes(width));
        return true;

      case BVSLT:
      case BVSLE:
      case BVSGT:
      case BVSGE:
      {
        CBV signedMin = CONSTANTBV::BitVector_Create(width, true);
        CONSTANTBV::BitVector_Bit_On(signedMin, width - 1);
        CBV signedMax = allOnes(width);
        CONSTANTBV::BitVector_Bit_Off(signedMax, width - 1);
        out.push_back(signedMin);
        out.push_back(signedMax);
        return true;
      }

      case BVLEFTSHIFT:
      case BVRIGHTSHIFT:
      case BVSRSHIFT:
        return shiftStandIns(n, index, children, out);

      default:
        break;
    }

    // Anything else: every value of the width, when there are few enough
    // of them. A wider child would push the result past what a set holds.
    if (width > SMALL_WIDTH)
      return false;
    for (uint64_t v = 0; v < (1ull << width); v++)
      out.push_back(valueOf(width, v));
    return true;
  }

  bool ValueSetAnalysis::shiftStandIns(const ASTNode& n, size_t index,
                                       const vector<const ValueSet*>& children,
                                       vector<CBV>& out)
  {
    const Kind k = n.GetKind();
    const unsigned width = n.GetValueWidth();

    if (index == 1)
    {
      // The amount. Shifting by the width or more always gives the same
      // answer, so the amounts to try stop there.
      if (children[0] == nullptr)
        return false;
      if ((width + 1) * children[0]->size() > PRODUCT_CAP)
        return false;
      for (unsigned s = 0; s <= width; s++)
        out.push_back(valueOf(width, s));
      return true;
    }

    // The value being shifted. Only the bits that survive the smallest of
    // the amounts can reach the result, so only those are worth varying.
    if (children[1] == nullptr)
      return false;

    unsigned smallest = width;
    for (const CBV s : children[1]->values)
      smallest = std::min(smallest, shiftAmount(s, width));

    // Shifted all the way out, an arithmetic shift still copies the sign
    // bit, so that bit always has to be varied.
    if (BVSRSHIFT == k && smallest == width)
      smallest = width - 1;

    const unsigned survivors = width - smallest;
    if (survivors > SMALL_WIDTH)
      return false;

    for (uint64_t v = 0; v < (1ull << survivors); v++)
    {
      CBV value = CONSTANTBV::BitVector_Create(width, true);
      for (unsigned i = 0; i < survivors; i++)
        if ((v >> i) & 1)
          CONSTANTBV::BitVector_Bit_On(value,
                                       BVLEFTSHIFT == k ? i : i + smallest);
      out.push_back(value);
    }
    return true;
  }

  // Takes ownership of "set".
  ValueSet* ValueSetAnalysis::expand(ValueSet* set, Expand how)
  {
    const unsigned width = set->getWidth();
    ValueSet* result = new ValueSet(width, set->isBoolean());

    for (const CBV member : set->values)
    {
      // The bits the unknown operand is free to change.
      vector<unsigned> free;
      for (unsigned i = 0; i < width; i++)
      {
        const bool one = CONSTANTBV::BitVector_bit_test(member, i);
        if (Expand::Submask == how ? one : !one)
          free.push_back(i);
      }

      // Two to the power of that many members: past three bits it can't
      // fit in a set anyway.
      if (free.size() > 31 || (1ull << free.size()) > ValueSet::MAX_ELEMENTS)
      {
        delete result;
        delete set;
        return nullptr;
      }

      for (uint64_t v = 0; v < (1ull << free.size()); v++)
      {
        CBV variant = CONSTANTBV::BitVector_Clone(member);
        for (unsigned b = 0; b < free.size(); b++)
        {
          const bool set_bit = ((v >> b) & 1) != 0;
          if (Expand::Submask == how)
          {
            if (!set_bit)
              CONSTANTBV::BitVector_Bit_Off(variant, free[b]);
          }
          else if (set_bit)
            CONSTANTBV::BitVector_Bit_On(variant, free[b]);
        }

        if (!result->insert(variant))
        {
          delete result;
          delete set;
          return nullptr;
        }
      }
    }

    delete set;
    return result;
  }

  ValueSet* ValueSetAnalysis::dispatchToTransferFunctions(
      const ASTNode& n, const vector<const ValueSet*>& children)
  {
    const Kind k = n.GetKind();

    if (BVCONST == k)
    {
      ValueSet* result = fresh(n);
      result->insert(CONSTANTBV::BitVector_Clone(n.GetBVConst()));
      propagated++;
      return result;
    }

    if (TRUE == k || FALSE == k)
    {
      ValueSet* result = fresh(n);
      CBV v = CONSTANTBV::BitVector_Create(1, true);
      if (TRUE == k)
        CONSTANTBV::BitVector_Bit_On(v, 0);
      result->insert(v);
      propagated++;
      return result;
    }

    if (ITE == k)
    {
      // The condition selects a branch when it's known; otherwise the
      // node can take any value from either branch.
      const ValueSet* condition = children[0];
      if (condition != nullptr && condition->isConstant())
      {
        const ValueSet* branch =
            CONSTANTBV::BitVector_bit_test(condition->smallest(), 0)
                ? children[1]
                : children[2];
        if (branch == nullptr)
          return nullptr;

        ValueSet* result = fresh(n);
        for (const CBV m : branch->values)
        {
          bool fitted = result->insert(CONSTANTBV::BitVector_Clone(m));
          assert(fitted);
          (void)fitted;
        }
        propagated++;
        return result;
      }

      if (children[1] == nullptr || children[2] == nullptr)
        return nullptr;

      ValueSet* result = fresh(n);
      for (int branch = 1; branch <= 2; branch++)
        for (const CBV m : children[branch]->values)
          if (!result->insert(CONSTANTBV::BitVector_Clone(m)))
          {
            delete result;
            widened++;
            return nullptr;
          }
      propagated++;
      return result;
    }

    if (!constEvaluable(k) || n.Degree() == 0)
      return nullptr;

    // Values standing in for the children nothing is known about.
    struct Owned
    {
      vector<vector<CBV>> values;
      ~Owned()
      {
        for (const vector<CBV>& v : values)
          for (const CBV c : v)
            CONSTANTBV::BitVector_Destroy(c);
      }
    } standIn;
    standIn.values.resize(children.size());

    Expand expandWith = Expand::None;
    for (size_t i = 0; i < children.size(); i++)
      if (children[i] == nullptr &&
          !standIns(n, i, children, standIn.values[i], expandWith))
      {
        widened++;
        return nullptr;
      }

    // What each child ranges over.
    vector<const vector<CBV>*> members(children.size());
    size_t combinations = 1;
    for (size_t i = 0; i < children.size(); i++)
    {
      members[i] = (children[i] != nullptr) ? &children[i]->values
                                            : &standIn.values[i];
      combinations *= members[i]->size();
      if (combinations > PRODUCT_CAP)
      {
        widened++;
        return nullptr;
      }
    }

    // Evaluate the node over each combination of the children's values.
    ValueSet* result = fresh(n);
    vector<CBV> combination(children.size());
    vector<size_t> odometer(children.size(), 0);
    for (size_t count = 0; count < combinations; count++)
    {
      for (size_t i = 0; i < children.size(); i++)
        combination[i] = (*members[i])[odometer[i]];

      if (!result->insert(evalOnCBVs(k, n, combination)))
      {
        delete result;
        widened++;
        return nullptr;
      }

      // Holding every value of the width already, the set says exactly
      // what a null pointer says, and the remaining combinations can't
      // change that -- which is where an evaluation of a comparison
      // usually ends up.
      if (result->isComplete())
      {
        delete result;
        widened++;
        return nullptr;
      }

      for (size_t i = 0; i < odometer.size(); i++)
      {
        if (++odometer[i] < members[i]->size())
          break;
        odometer[i] = 0;
      }
    }

    if (Expand::None != expandWith)
      result = expand(result, expandWith);

    // A set holding every value of its width says exactly what a null
    // pointer says.
    if (result == nullptr || result->isComplete())
    {
      delete result;
      widened++;
      return nullptr;
    }

    propagated++;
    return result;
  }

  void ValueSetAnalysis::stats()
  {
    std::cerr << "{ValueSetAnalysis} Propagated: " << propagated << std::endl;
    std::cerr << "{ValueSetAnalysis} Widened: " << widened << std::endl;
  }
}

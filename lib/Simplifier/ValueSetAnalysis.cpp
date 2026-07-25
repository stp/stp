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

  // A constant node with the member's value, suitable as an argument of
  // the constant evaluator.
  ASTNode ValueSetAnalysis::toNode(const ASTNode& child, const CBV member)
  {
    if (BOOLEAN_TYPE == child.GetType())
      return CONSTANTBV::BitVector_bit_test(member, 0) ? bm.ASTTrue
                                                       : bm.ASTFalse;
    return bm.CreateBVConst(CONSTANTBV::BitVector_Clone(member),
                            child.GetValueWidth());
  }

  // The evaluated constant's value as a fresh CBV the caller owns.
  CBV ValueSetAnalysis::toCBV(const ASTNode& evaluated)
  {
    if (TRUE == evaluated.GetKind())
    {
      CBV r = CONSTANTBV::BitVector_Create(1, true);
      CONSTANTBV::BitVector_Bit_On(r, 0);
      return r;
    }
    if (FALSE == evaluated.GetKind())
      return CONSTANTBV::BitVector_Create(1, true);

    assert(BVCONST == evaluated.GetKind());
    return CONSTANTBV::BitVector_Clone(evaluated.GetBVConst());
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

    // Constant nodes for every child's member, built once.
    vector<vector<ASTNode>> constants(children.size());
    for (size_t i = 0; i < children.size(); i++)
      for (const CBV m : *members[i])
        constants[i].push_back(toNode(n[i], m));

    // Evaluate the node over each combination of the children's values.
    ValueSet* result = fresh(n);
    vector<size_t> odometer(children.size(), 0);
    for (size_t count = 0; count < combinations; count++)
    {
      ASTVec combination;
      combination.reserve(children.size());
      for (size_t i = 0; i < children.size(); i++)
        combination.push_back(constants[i][odometer[i]]);

      const ASTNode evaluated =
          NonMemberBVConstEvaluator(&bm, k, combination, n.GetValueWidth());

      if (!result->insert(toCBV(evaluated)))
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

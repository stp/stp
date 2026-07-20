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

    size_t combinations = 1;
    for (const ValueSet* c : children)
    {
      if (c == nullptr)
        return nullptr;
      combinations *= c->size();
      if (combinations > PRODUCT_CAP)
        return nullptr;
    }

    // Constant nodes for every child's member, built once.
    vector<vector<ASTNode>> constants(children.size());
    for (size_t i = 0; i < children.size(); i++)
      for (const CBV m : children[i]->values)
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
        if (++odometer[i] < children[i]->size())
          break;
        odometer[i] = 0;
      }
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

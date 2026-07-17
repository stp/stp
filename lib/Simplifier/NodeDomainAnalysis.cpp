/********************************************************************
 * AUTHORS: Trevor Hansen
 *
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



#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"

namespace stp
{

  // True if the two domains have an intersection, i.e. share >=1 value.
  bool intersects(FixedBits * bits, UnsignedInterval * interval)
  {
   if (bits == nullptr || interval == nullptr)
        return true; // nothing to do.

    assert(bits->getWidth() == interval->getWidth());
    bool result = true;

    CBV max = bits->GetMaxBVConst();
    CBV min = bits->GetMinBVConst();

    if (CONSTANTBV::BitVector_Lexicompare(max, interval->minV) < 0)
      result = false;
  
    if (CONSTANTBV::BitVector_Lexicompare(interval->maxV, min) < 0)
      result = false;

    CONSTANTBV::BitVector_Destroy(min);
    CONSTANTBV::BitVector_Destroy(max);
    return result;
  }

  // The largest value that matches the fixed bits and is <= bound,
  // or nullptr if there is no such value. Caller destroys the result.
  static CBV maxBelow(const FixedBits& bits, const CBV bound)
  {
    const int width = bits.getWidth();

    // The highest bit where the fixed bits differ from the bound.
    int mismatch = -1;
    for (int i = width - 1; i >= 0; i--)
      if (bits.isFixed(i) &&
          bits.getValue(i) != CONSTANTBV::BitVector_bit_test(bound, i))
      {
        mismatch = i;
        break;
      }

    if (mismatch == -1)
      return CONSTANTBV::BitVector_Clone(bound);

    // The result equals the bound above "diverge", goes below the bound
    // at "diverge", and is maximised underneath.
    int diverge;
    if (!bits.getValue(mismatch))
      diverge = mismatch; // the fixed zero takes it below the bound.
    else
    {
      // The fixed one takes it above the bound, so an unfixed bit
      // higher up must go below instead. The lowest such bit loses the
      // least.
      diverge = -1;
      for (int j = mismatch + 1; j < width; j++)
        if (!bits.isFixed(j) && CONSTANTBV::BitVector_bit_test(bound, j))
        {
          diverge = j;
          break;
        }
      if (diverge == -1)
        return nullptr;
    }

    CBV result = CONSTANTBV::BitVector_Create(width, true);
    for (int i = 0; i < width; i++)
    {
      bool bit;
      if (i > diverge)
        bit = CONSTANTBV::BitVector_bit_test(bound, i);
      else if (i == diverge)
        bit = false;
      else
        bit = bits.isFixed(i) ? bits.getValue(i) : true;
      if (bit)
        CONSTANTBV::BitVector_Bit_On(result, i);
    }
    return result;
  }

  // The smallest value that matches the fixed bits and is >= bound,
  // or nullptr if there is no such value. Caller destroys the result.
  static CBV minAbove(const FixedBits& bits, const CBV bound)
  {
    const int width = bits.getWidth();

    int mismatch = -1;
    for (int i = width - 1; i >= 0; i--)
      if (bits.isFixed(i) &&
          bits.getValue(i) != CONSTANTBV::BitVector_bit_test(bound, i))
      {
        mismatch = i;
        break;
      }

    if (mismatch == -1)
      return CONSTANTBV::BitVector_Clone(bound);

    // The result equals the bound above "diverge", goes above the bound
    // at "diverge", and is minimised underneath.
    int diverge;
    if (bits.getValue(mismatch))
      diverge = mismatch; // the fixed one takes it above the bound.
    else
    {
      diverge = -1;
      for (int j = mismatch + 1; j < width; j++)
        if (!bits.isFixed(j) && !CONSTANTBV::BitVector_bit_test(bound, j))
        {
          diverge = j;
          break;
        }
      if (diverge == -1)
        return nullptr;
    }

    CBV result = CONSTANTBV::BitVector_Create(width, true);
    for (int i = 0; i < width; i++)
    {
      bool bit;
      if (i > diverge)
        bit = CONSTANTBV::BitVector_bit_test(bound, i);
      else if (i == diverge)
        bit = true;
      else
        bit = bits.isFixed(i) ? bits.getValue(i) : false;
      if (bit)
        CONSTANTBV::BitVector_Bit_On(result, i);
    }
    return result;
  }

  // Whether some value matches the fixed bits and lies within [min, max].
  static bool hasMemberInRange(const FixedBits& bits, const CBV min,
                               const CBV max)
  {
    CBV smallest = minAbove(bits, min);
    if (smallest == nullptr)
      return false;
    const bool result = CONSTANTBV::BitVector_Lexicompare(smallest, max) <= 0;
    CONSTANTBV::BitVector_Destroy(smallest);
    return result;
  }

  // Trim each domain to exactly the values the two domains share: the
  // interval becomes [min, max] of the shared values, and a bit is fixed
  // whenever every shared value agrees on it. Assumes the domains share
  // at least one value. Idempotent.
  void NodeDomainAnalysis::harmonise(FixedBits * &bits, UnsignedInterval * &interval)
  {
      if (bits == nullptr && interval == nullptr)
        return; // no information, nothing can be done..

      if (bits != nullptr && interval != nullptr)
      {
        assert(intersects(bits, interval));

        if (bits->isTotallyFixed() && interval->isConstant())
          return; // full information already.
      }

      if (bits != nullptr)
      {
        const auto width = bits->getWidth();

        if (interval == nullptr)
            interval = new UnsignedInterval(width);

        // The least and greatest values the domains share.
        CBV max = maxBelow(*bits, interval->maxV);
        CBV min = minAbove(*bits, interval->minV);

        // The domains share a value, so both exist.
        assert(max != nullptr && min != nullptr);

        if (max != nullptr)
        {
          if (interval->replaceMaxIfTightens(max))
            tighten++;
          CONSTANTBV::BitVector_Destroy(max);
        }
        if (min != nullptr)
        {
          if (interval->replaceMinIfTightens(min))
            tighten++;
          CONSTANTBV::BitVector_Destroy(min);
        }
      }

      if (interval != nullptr && !interval->isComplete())
      {
        if (bits == nullptr)
        {
          bits = new FixedBits(interval->getWidth(),false); /// TODO do we really need to know if it's boolean??
        }

        // Fix each bit that all the shared values agree on. The interval
        // is already exactly the range of the shared values, so a bit
        // can take a polarity iff fixing it that way leaves a value
        // matching the fixed bits inside the interval.
        const unsigned width = bits->getWidth();
        for (unsigned i = 0; i < width; i++)
        {
          if (bits->isFixed(i))
            continue;

          bits->setFixed(i, true);
          bits->setValue(i, false);
          const bool canBeZero =
              hasMemberInRange(*bits, interval->minV, interval->maxV);
          bits->setValue(i, true);
          const bool canBeOne =
              hasMemberInRange(*bits, interval->minV, interval->maxV);

          assert(canBeZero || canBeOne); // the domains share a value.

          if (canBeZero == canBeOne)
            bits->setFixed(i, false);
          else
          {
            bits->setValue(i, canBeOne);
            tighten++;
          }
        }
      }

      if (bits != nullptr && bits->countFixed() == 0)
      {
        delete bits;
        bits = nullptr;
      }

      assert(intersects(bits, interval));
  }

  std::pair<FixedBits*, UnsignedInterval*> NodeDomainAnalysis::buildMap(const ASTNode& n)
  {
    {
      auto it = toFixedBits.find(n);
      if (it != toFixedBits.end())
      {
        auto it0 = toIntervals.find(n);
        return {it->second, it0->second};
      }
    }

    const auto number_children = n.Degree();

    vector<FixedBits*> children_bits;
    children_bits.reserve(number_children);

    vector<const UnsignedIntervalSet*> children_sets;
    children_sets.reserve(number_children);

    bool nothingKnown = true;

    for (unsigned i = 0; i < number_children; i++)
    {
      auto ret = buildMap(n[i]);
      auto op0 = ret.first;
      auto op1 = ret.second;

      if (op0 != nullptr || op1 != nullptr)
        nothingKnown = false;

      children_bits.push_back(op0);

      const UnsignedIntervalSet* childSet = nullptr;
      auto sit = toIntervalSets.find(n[i]);
      if (sit != toIntervalSets.end())
        childSet = sit->second;
      children_sets.push_back(childSet);
    }

    const bool nullChildZero = (number_children > 0) && (children_bits[0] == nullptr && children_sets[0] == nullptr);

    // We need to know something about the children if we want to know something about the parent.
    // extract, bvsx, and bvzx all have constants as children.
    if ((n.GetKind() == READ) 
      ||(n.GetKind() == WRITE) 
      ||(number_children > 0 && nothingKnown) 
      ||(n.GetKind() == BVEXTRACT && nullChildZero) 
      ||(n.GetKind() == BVSX && nullChildZero) 
      ||(n.GetKind() == BVZX && nullChildZero) 
      ||(n.GetKind() == SYMBOL))
    {
      toFixedBits.insert({n, nullptr});
      toIntervals.insert({n, nullptr});
      toIntervalSets.insert({n, nullptr});

      return {nullptr, nullptr};
    }

    FixedBits* result_bits = fresh(n);

    if (n.GetKind() == BVCONST)
    {
      // the CBV doesn't leak. it is a copy of the cbv inside the node.
      CBV cbv = n.GetBVConst();

      for (unsigned int j = 0; j < n.GetValueWidth(); j++)
      {
        result_bits->setFixed(j, true);
        result_bits->setValue(j, CONSTANTBV::BitVector_bit_test(cbv, j));
      }
    }
    else if (TRUE == n.GetKind())
    {
      result_bits->setFixed(0, true);
      result_bits->setValue(0, true);
    }
    else if (FALSE == n.GetKind())
    {
      result_bits->setFixed(0, true);
      result_bits->setValue(0, false);
    }
    else
    {
      for (unsigned i = 0; i < number_children; i++)
      {
        // interval transfer function doesn't care about null.
        
        if (children_bits[i] == nullptr)
          children_bits[i] = getEmptyFixedBits(n[i]);
      }

      if (n.GetKind() == BVMULT)
      {
        simplifier::constantBitP::MultiplicationStatsMap msm;
        simplifier::constantBitP::ConstantBitPropagation::
            dispatchToTransferFunctions(&bm, n.GetKind(), children_bits, *result_bits, n,
                                        &msm);
      }
      else
      {
        simplifier::constantBitP::ConstantBitPropagation::
            dispatchToTransferFunctions(&bm, n.GetKind(), children_bits, *result_bits, n,
                                        nullptr);
      }
    }

    if (result_bits->isTotallyUnfixed())
    {
      delete result_bits;
      result_bits = nullptr;
    }

    // The interval-set transfer runs the single-interval transfer functions
    // over the cross-product of the children's disjoint pieces; the node's
    // interval is the set's hull, which refines (never loosens) the plain
    // single-interval result.
    UnsignedIntervalSet* result_set = setAnalysis.transfer(n, children_sets);

    UnsignedInterval* result_interval = result_set->hull(); // null if complete

    assert(intersects(result_bits, result_interval));

    harmonise(result_bits, result_interval);

    // Keep the stored set within the harmonised interval so the two agree.
    if (result_interval != nullptr)
      result_set->intersectInterval(result_interval->minV, result_interval->maxV);

    toFixedBits.insert({n, result_bits});
    toIntervals.insert({n, result_interval});
    toIntervalSets.insert({n, result_set});

    if (n.isConstant())
    {
      assert(result_bits->isTotallyFixed());
      assert(result_interval->isConstant());
    }

    return {result_bits, result_interval};
  }

  // When we call the transfer functions, we can't send nulls, send unfixed instead.
  FixedBits* NodeDomainAnalysis::getEmptyFixedBits(const ASTNode& n)
  {
    if (n.GetType() == BOOLEAN_TYPE)
    {
      assert(emptyBoolean->isTotallyUnfixed());
      return emptyBoolean;
    }
    if (emptyBitVector.find(n.GetValueWidth()) == emptyBitVector.end())
      emptyBitVector[n.GetValueWidth()] = fresh(n);

    FixedBits* r = emptyBitVector[n.GetValueWidth()];
    assert(r->isTotallyUnfixed());
    return r;
  }

  void NodeDomainAnalysis::stats()
  {
    if (bm.UserFlags.stats_flag)
    {
      std::cerr << "{NodeDomainAnalysis} Tightened:" << tighten << std::endl;

      intervalAnalysis.stats();
    }
  }
}

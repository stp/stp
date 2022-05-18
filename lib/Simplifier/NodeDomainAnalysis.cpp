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

  // True if the two domains have an intersection.
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

  // Trim so the min/max of each domain matches. 
  void NodeDomainAnalysis::harmonise(FixedBits * &bits, UnsignedInterval * &interval)
  {
      if (bits == nullptr && interval == nullptr)
        return; // nothing to do.

      bool changed= false;

      if (bits != nullptr)
      {
        // Get the minimum and maximum from the fixedbits
        // Change the unsigned interval to them if they're tigher.
        
        CBV max = bits->GetMaxBVConst();
        CBV min = bits->GetMinBVConst();
        
        if (interval == nullptr) 
        {
            interval = new UnsignedInterval(min,max);
            changed =true;
        }
        else
        {
          changed = interval->replaceMaxIfTightens(max);
          changed = interval->replaceMinIfTightens(min) || changed;

          CONSTANTBV::BitVector_Destroy(min);
          CONSTANTBV::BitVector_Destroy(max);
        }
      }
      
      if (interval != nullptr)
      {
          // differently to the previous case, it's possible to have an interval with a complete fixedbits.
      }

      //if(changed)
        //harmonise(bits,interval);

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

    vector<const UnsignedInterval*> children_intervals;
    children_intervals.reserve(number_children);

    bool nothingKnown = true;

    for (unsigned i = 0; i < number_children; i++)
    {
      auto ret = buildMap(n[i]);
      auto op0 = ret.first;
      auto op1 = ret.second;

      if (op0 != nullptr || op1 != nullptr)
        nothingKnown = false;
      
      children_bits.push_back(op0);
      children_intervals.push_back(op1);
    }

    const bool nullChildZero = (number_children > 0) && (children_bits[0] == nullptr && children_intervals[0] == nullptr);

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

    UnsignedInterval* result_interval = intervalAnalysis.dispatchToTransferFunctions(n, children_intervals);

    if (result_interval != nullptr && result_interval->isComplete())
    {
      delete result_interval;
      result_interval = nullptr;
    }

    assert(intersects(result_bits, result_interval));

    harmonise(result_bits, result_interval);

    toFixedBits.insert({n, result_bits});
    toIntervals.insert({n, result_interval});

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
}

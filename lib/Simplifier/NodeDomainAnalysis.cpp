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

namespace simplifier
{
  namespace constantBitP
  {
    Result fix(FixedBits& b, stp::CBV low, stp::CBV high);
  }
}

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

  // Trim so the min/max of both domains are consistent with each other.
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

      bool changed=false;

      // Tighten the intervals using the fixed bit information.
      if (bits != nullptr)
      {
        const auto width = bits->getWidth();

        if (interval == nullptr) 
            interval = new UnsignedInterval(width);

        // (1) Cheap attempt to tighten intervals.
        CBV max = bits->GetMaxBVConst();
        CBV min = bits->GetMinBVConst();
        if (interval->replaceMaxIfTightens(max))
          tighten++;
        if (interval->replaceMinIfTightens(min))
          tighten++;
        CONSTANTBV::BitVector_Destroy(min);
        CONSTANTBV::BitVector_Destroy(max);

        // (2) More comprehensive is required because cheap (1) isn't enough.
        if(!bits->in(interval->maxV))
        {
          const stp::CBV max = bits->GetMaxBVConst();
          assert( width > 1 ); // i don't think can come in here otherwise.
          
          stp::CBV result = CONSTANTBV::BitVector_Create(width, true);
          bool reduced = false;
          for (int i = width-1; i >=0 ; i--)
          {
            const bool bit = CONSTANTBV::BitVector_bit_test(interval->maxV, i);
            if (bits->isFixed(i))
            {
              if (bits->getValue(i))
              {
                  CONSTANTBV::BitVector_Bit_On(result,i);
                  if (!bit && !reduced)
                  {
                     // We are increasing the result. So we need to reduce above.
                    for (unsigned j = i+1 ; j <= width-1 ; j++)
                    {
                      if (bits->isFixed(j))   
                        continue;
                      const bool bv = CONSTANTBV::BitVector_bit_test(interval->maxV, j);
                      if (bv)
                      {
                        CONSTANTBV::BitVector_Bit_Off(result,j);
                        reduced = true;
                        break;
                      }
                      else
                        CONSTANTBV::BitVector_Bit_On(result,j);
                    }
                    assert(reduced);
                  }
              }
              else
              {
                  CONSTANTBV::BitVector_Bit_Off(result,i);
                  if (bit)
                    reduced=true;
              }
            }
            else
            {
              if (reduced || bit)
                 CONSTANTBV::BitVector_Bit_On(result,i);
              else
                CONSTANTBV::BitVector_Bit_Off(result,i);
            }
          }

          // The old max must be greater or equal to the new max.
          assert (CONSTANTBV::BitVector_Lexicompare(max, result) > 0); 
          assert (bits->in(result)); 

          interval->replaceMaxIfTightens(result);
          CONSTANTBV::BitVector_Destroy(result);
          CONSTANTBV::BitVector_Destroy(max);
          tighten++;
        }
        if(!bits->in(interval->minV))
        {
            //TODO - still need to do it on the minimimum.
            todo++;
        }
      }
    
      if (interval != nullptr)
      {
        if (bits == nullptr)
        {
          bits = new FixedBits(interval->getWidth(),false); /// TODO do we really need to know if it's boolean??
        }
        const auto last = bits->countFixed();
        simplifier::constantBitP::fix(*bits, interval->minV, interval->maxV);
        if (bits->countFixed() != last)
        {
          changed = true;
          tighten++;
        }
        if (bits->countFixed() == 0)
        {
          delete bits;
          bits = nullptr;
        }
      }
    
      assert(intersects(bits, interval));
      if (changed)
        harmonise(bits, interval);
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

  void NodeDomainAnalysis::stats()
  {
    if (bm.UserFlags.stats_flag)
    {
      std::cerr << "{NodeDomainAnalysis} TODO:" << todo << std::endl;
      std::cerr << "{NodeDomainAnalysis} Tightened:" << tighten << std::endl;

      intervalAnalysis.stats();
    }
  }
}

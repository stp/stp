/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Februrary, 2011
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

/*
 * Performs a basic unsigned interval analysis.
 * The analysis is only bottom up (without assuming that the root node is true).
 * Some of the transfer functions are approximations (they're marked with comments).
 */

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/StrengthReduction.h"
#include <iostream>
#include <map>
#include <cmath>

using std::map;

namespace stp
{

  using NodeToUnsignedIntervalMap = std::unordered_map<const ASTNode, UnsignedInterval*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;

  void UnsignedIntervalAnalysis::stats()
  {
    std::cerr << "{UnsignedIntervalAnalysis} TODO propagator not implemented: "
              << propagatorNotImplemented << std::endl;
    std::cerr << "{UnsignedIntervalAnalysis} Iterations: " << iterations
              << std::endl;
  }

  using std::make_pair;

  UnsignedInterval* UnsignedIntervalAnalysis::freshUnsignedInterval(unsigned width)
  {
    width = std::max((unsigned)1, width);
    UnsignedInterval* it = createInterval(getEmptyCBV(width), getEmptyCBV(width));
    CONSTANTBV::BitVector_Fill(it->maxV);
    return it;
  }

  // Doesn't take ownership of the CBVs.
  // Doesn't own the returned.
  UnsignedInterval* UnsignedIntervalAnalysis::createInterval(CBV min, CBV max)
  {
    return new UnsignedInterval(CONSTANTBV::BitVector_Clone(min), CONSTANTBV::BitVector_Clone(max));
  }

  // readonly.
  CBV UnsignedIntervalAnalysis::getEmptyCBV(unsigned width)
  {
    width = std::max(width, (unsigned)1);

    if (emptyCBV.find(width) == emptyCBV.end())
    {
      emptyCBV[width] = CONSTANTBV::BitVector_Create(width, true);
    }
    
    assert(CONSTANTBV::BitVector_is_empty(emptyCBV[width]));  
    return emptyCBV[width];
  }

  //readonly
  UnsignedInterval* UnsignedIntervalAnalysis::getEmptyInterval(const ASTNode& n)
  {
    const auto width = std::max((unsigned)1,n.GetValueWidth());

    if (emptyIntervals.find(width) == emptyIntervals.end())
    {
      stp::CBV min = CONSTANTBV::BitVector_Create(width, true);
      stp::CBV max = CONSTANTBV::BitVector_Create(width, true);
      CONSTANTBV::BitVector_Fill(max);
      emptyIntervals[width] = new UnsignedInterval(min,max);
    }

    UnsignedInterval* r = emptyIntervals[width];
    assert(r->isComplete());
    return r;
  }

  // Replace some of the things that unsigned intervals can figure out for us.
  ASTNode UnsignedIntervalAnalysis::topLevel(const ASTNode& top)
  {
    propagatorNotImplemented = 0;
    iterations=0;

    bm.GetRunTimes()->start(RunTimes::IntervalPropagation);

    NodeToUnsignedIntervalMap visited;
    visit(top, visited);

    if (bm.UserFlags.stats_flag)
      stats();

    StrengthReduction sr(bm.defaultNodeFactory, &bm.UserFlags);
    ASTNode result = sr.topLevel(top, visited);

    bm.GetRunTimes()->stop(RunTimes::IntervalPropagation);

    return result;
  }

  UnsignedInterval* UnsignedIntervalAnalysis::dispatchToTransferFunctions(const ASTNode&n, const vector<const UnsignedInterval*>& _children)
  {
    const auto number_children = n.Degree();    
    const auto width = n.GetValueWidth();
    const bool knownC0 = number_children < 1 ? false : (_children[0] != NULL);
    const bool knownC1 = number_children < 2 ? false : (_children[1] != NULL);
    const bool knownC2 = number_children < 3 ? false : (_children[2] != NULL);

    assert(number_children == _children.size());

    // Put in temporary null ones for any we're missing.
    auto children = _children;
    for (unsigned i =0 ; i < number_children; i++)
    {
      if (children[i] == nullptr)
        children[i] = getEmptyInterval(n[i]);
    }

    iterations++;

    UnsignedInterval* result = nullptr;

    switch (n.GetKind())
    {
      case BVCONST:
      case BITVECTOR:
      {
        // the CBV doesn't leak. it is a copy of the cbv inside the node.
        CBV cbv = n.GetBVConst();
        result = createInterval(cbv, cbv);
      }
      break;

      case TRUE:
        result = createInterval(littleOne, littleOne);
        break;

      case FALSE:
        result = createInterval(littleZero, littleZero);
        break;

      case NOT:
        if (knownC0)
        {
          assert(children[0]->isConstant());
          if (!CONSTANTBV::BitVector_Lexicompare(children[0]->minV, littleOne))
            result = createInterval(littleZero, littleZero);
          else
            result = createInterval(littleOne, littleOne);
        }
        break;

      case EQ:
        if (knownC0 && knownC1)
        {
          if ((CONSTANTBV::BitVector_Lexicompare(children[1]->minV,
                                                 children[0]->maxV) > 0) ||
              (CONSTANTBV::BitVector_Lexicompare(children[0]->minV,
                                                 children[1]->maxV) > 0))
            result = createInterval(littleZero, littleZero);

          else if (children[0]->isConstant() && children[1]->isConstant() &&
                   CONSTANTBV::BitVector_Lexicompare(children[0]->minV,
                                                     children[1]->minV) == 0)
          {
            result = createInterval(littleOne, littleOne);
          }
        }
        break;

      case BVGT:
        {
          const UnsignedInterval *c0 = children[0];
          const UnsignedInterval *c1 = children[1];

          if (CONSTANTBV::BitVector_Lexicompare(c0->minV, c1->maxV) > 0)
            result = createInterval(littleOne, littleOne);

          if (CONSTANTBV::BitVector_Lexicompare(c1->minV, c0->maxV) >= 0)
            result = createInterval(littleZero, littleZero);
        }

        break;

      case BVSGT: 
        {
          vector<UnsignedInterval*> a_vec, b_vec;
          UnsignedInterval::split(children[0],a_vec); // split at the poles
          UnsignedInterval::split(children[1],b_vec); 
             
          bool one = false;
          bool zero = false;        
          for (const auto& a : a_vec)
            for (const auto& b : b_vec) /// compare all pairs.
            {
              if (CONSTANTBV::BitVector_Compare(a->minV, b->maxV) > 0) // signed comparison.
                one = true;
              else if (CONSTANTBV::BitVector_Compare(b->minV, a->maxV) >= 0)
                zero = true;
              else
              {
                one = true;
                zero = true;
                break;
              }
            }

          if (one && !zero)
            result = createInterval(littleOne, littleOne);

          if (!one && zero)
            result = createInterval(littleZero, littleZero);

          for (const auto& a : a_vec)
            delete a;
          for (const auto& b : b_vec)
            delete b;     
        }
        break;

      case BVDIV:
      {
        const UnsignedInterval* c1 =  children[1];

        result = freshUnsignedInterval(width);

        CBV c1Min = CONSTANTBV::BitVector_Clone(c1->minV);
        bool bottomChanged = false;
        if (CONSTANTBV::BitVector_is_empty(c1->minV))
        {
          if (CONSTANTBV::BitVector_is_empty(c1->maxV))
          {
            CONSTANTBV::BitVector_Fill(result->minV);
            CONSTANTBV::BitVector_Fill(result->maxV);
            CONSTANTBV::BitVector_Destroy(c1Min);
            break; // result is [1111..111, 11...11111]
          }

          bottomChanged = true;
          CONSTANTBV::BitVector_Destroy(c1Min);
          break; // TODO fix so that it can run-on.
        }

        const UnsignedInterval* top = children[0];
        result->resetToComplete();

        CBV remainder = CONSTANTBV::BitVector_Create(width, true);

        CBV tmp0 = CONSTANTBV::BitVector_Clone(top->minV);
        CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(
            result->minV, tmp0, c1->maxV, remainder);
        assert(0 == e);
        CONSTANTBV::BitVector_Destroy(tmp0);

        tmp0 = CONSTANTBV::BitVector_Clone(top->maxV);
        e = CONSTANTBV::BitVector_Div_Pos(result->maxV, tmp0, c1Min, remainder);
        assert(0 == e);

        CONSTANTBV::BitVector_Destroy(tmp0);
        CONSTANTBV::BitVector_Destroy(remainder);

        if (bottomChanged) // might have been zero.
        {
          if (CONSTANTBV::BitVector_Lexicompare(result->minV, c1Min) > 0)
          {
            CONSTANTBV::BitVector_Copy(result->minV,
                                       c1Min); //c1 should still be 1
          }

          if (CONSTANTBV::BitVector_Lexicompare(result->maxV, c1Min) < 0)
          {
            CONSTANTBV::BitVector_Copy(result->maxV,
                                       c1Min); //c1 should still be 1
          }
        }
        CONSTANTBV::BitVector_Destroy(c1Min);

        break;
      }

      case BVMOD: //OVER-APPROXIMATION
        if (knownC1)
        {
          // When we're dividing by zero, we know nothing.
          if (!CONSTANTBV::BitVector_is_empty(children[1]->minV))
          {
            result = freshUnsignedInterval(n.GetValueWidth());
            CONSTANTBV::BitVector_Copy(result->maxV, children[1]->maxV);
            CONSTANTBV::BitVector_decrement(result->maxV);

            // If the top is known, and it's maximum is less, use that.
            if (knownC0 &&
                CONSTANTBV::BitVector_Lexicompare(children[0]->maxV,
                                                  result->maxV) < 0)
              CONSTANTBV::BitVector_Copy(result->maxV, children[0]->maxV);
          }
        }
        break;

      case BVSX:
        if (knownC0)
        {
          result = freshUnsignedInterval(n.GetValueWidth());
          CONSTANTBV::BitVector_Empty(result->maxV);

          // Copy the max/min into the new bigger answer.
          for (unsigned i = 0; i < n[0].GetValueWidth(); i++)
          {
            if (CONSTANTBV::BitVector_bit_test(children[0]->maxV, i))
              CONSTANTBV::BitVector_Bit_On(result->maxV, i);

            if (CONSTANTBV::BitVector_bit_test(children[0]->minV, i))
              CONSTANTBV::BitVector_Bit_On(result->minV, i);
          }
          for (unsigned i = n[0].GetValueWidth(); i < n.GetValueWidth(); i++)
          {
            if (CONSTANTBV::BitVector_bit_test(children[0]->maxV,
                                               n[0].GetValueWidth() - 1))
              CONSTANTBV::BitVector_Bit_On(result->maxV, i);

            if (CONSTANTBV::BitVector_bit_test(children[0]->minV,
                                               n[0].GetValueWidth() - 1))
              CONSTANTBV::BitVector_Bit_On(result->minV, i);
          }
        }
        break;

      case BVNOT:
        if (knownC0) // NOT of the bitvector.
        {
          result = freshUnsignedInterval(width);
          CONSTANTBV::BitVector_Copy(result->maxV, children[0]->minV);
          CONSTANTBV::BitVector_Flip(result->maxV);
          CONSTANTBV::BitVector_Copy(result->minV, children[0]->maxV);
          CONSTANTBV::BitVector_Flip(result->minV);
        }
        break;

      case BVUMINUS:
        if (knownC0)
        {
          // Imagine it's {00, 01},  the unary minus of these is: {00,11},
          // i.e. it's everything. When there's a zero, (except for [0,0]),
          // it will be everything.

          if (!CONSTANTBV::BitVector_is_empty(children[0]->minV))
          {
            result = freshUnsignedInterval(width);
            CONSTANTBV::BitVector_Copy(result->maxV, children[0]->minV);
            CONSTANTBV::BitVector_Flip(result->maxV);
            CONSTANTBV::BitVector_increment(result->maxV);

            CONSTANTBV::BitVector_Copy(result->minV, children[0]->maxV);
            CONSTANTBV::BitVector_Flip(result->minV);
            CONSTANTBV::BitVector_increment(result->minV);
          }
          if ((CONSTANTBV::BitVector_is_empty(children[0]->minV)) &&
              (CONSTANTBV::BitVector_is_empty(children[0]->maxV)))
          {
            result = freshUnsignedInterval(width);
            CONSTANTBV::BitVector_Empty(result->maxV);
            CONSTANTBV::BitVector_Empty(result->minV);
          }
        }
        break;

      case ITE:
        if (knownC0)
        {
          result = freshUnsignedInterval(width);
          if (CONSTANTBV::BitVector_bit_test(children[0]->minV, 0) &&
              children[1] != NULL)
          {
            CONSTANTBV::BitVector_Copy(result->minV, children[1]->minV);
            CONSTANTBV::BitVector_Copy(result->maxV, children[1]->maxV);
          }
          else if (!CONSTANTBV::BitVector_bit_test(children[0]->minV, 0) &&
                   children[2] != NULL)
          {
            CONSTANTBV::BitVector_Copy(result->minV, children[2]->minV);
            CONSTANTBV::BitVector_Copy(result->maxV, children[2]->maxV);
          }
        }
        else if (knownC1 && knownC2)
        {
          // Both terms and propositions.
          result = freshUnsignedInterval(width);
          CBV min, max;
          if (CONSTANTBV::BitVector_Lexicompare(children[1]->minV,
                                                children[2]->minV) > 0)
            min = children[2]->minV;
          else
            min = children[1]->minV;

          if (CONSTANTBV::BitVector_Lexicompare(children[1]->maxV,
                                                children[2]->maxV) > 0)
            max = children[1]->maxV;
          else
            max = children[2]->maxV;

          CONSTANTBV::BitVector_Copy(result->minV, min);
          CONSTANTBV::BitVector_Copy(result->maxV, max);
        }
        break;

      case BVMULT: //OVER-APPROXIMATION
        if (knownC0 && knownC1)
        {
          //  >=2 arity.
          CBV min, max;
          min = CONSTANTBV::BitVector_Create(2 * width, true);
          max = CONSTANTBV::BitVector_Create(2 * width, true);

          // Make the result interval 1.
          result = freshUnsignedInterval(width);
          CONSTANTBV::BitVector_increment(result->minV);
          CONSTANTBV::BitVector_Flip(result->maxV);
          CONSTANTBV::BitVector_increment(result->maxV);

          bool bad = false;
          for (size_t i = 0; i < children.size(); i++)
          {
            if (children[i] == NULL)
            {
              bad = true;
              break;
            }
            CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Multiply(
                min, result->minV, children[i]->minV);
            assert(0 == e);

            e = CONSTANTBV::BitVector_Multiply(max, result->maxV,
                                               children[i]->maxV);
            assert(0 == e);

            if (CONSTANTBV::Set_Max(max) >= width)
              bad = true;

            for (unsigned j = width; j < 2 * width; j++)
            {
              if (CONSTANTBV::BitVector_bit_test(min, j))
                bad = true;
            }

            CONSTANTBV::BitVector_Interval_Copy(result->minV, min, 0, 0, width);
            CONSTANTBV::BitVector_Interval_Copy(result->maxV, max, 0, 0, width);
          }
          CONSTANTBV::BitVector_Destroy(min);
          CONSTANTBV::BitVector_Destroy(max);
          if (bad)
            {
              delete result;
              result = NULL;
            }
        }
        break;

      case AND:
      {
        // If any are definately zero then the answer is zero.
        for (unsigned i = 0; i < children.size(); i++)
          if (CONSTANTBV::BitVector_is_empty(children[i]->maxV))
          {
            result = createInterval(littleZero, littleZero);
            break;
          }
        // If all are definately one the answer is one.
        bool allok = true;
        for (unsigned i = 0; i < children.size(); i++)
          if (CONSTANTBV::BitVector_is_empty(children[i]->minV))
          {
            allok = false;
            break;
          }
        if (allok)
          result = createInterval(littleOne, littleOne);
      }
      break;

      case OR:
      {
        // If any are definately one then the answer is  one.
        for (unsigned i = 0; i < children.size(); i++)
          if (CONSTANTBV::BitVector_is_full(children[i]->minV))
          {
            result = createInterval(littleOne, littleOne);
            break;
          }
        // If all are definately false the answer is false.
        bool allfalse = true;
        for (unsigned i = 0; i < children.size(); i++)
          if (CONSTANTBV::BitVector_is_full(children[i]->maxV))
          {
            allfalse = false;
            break;
          }
        if (allfalse)
          result = createInterval(littleZero, littleZero);
      }
      break;

      case XOR:
      {
        bool allOK = true;
        unsigned count = 0;
        for (unsigned i = 0; i < children.size(); i++)
          if (children[i]->isConstant())
          {
            if (!CONSTANTBV::BitVector_is_empty(children[i]->maxV))
              count++;
          }
          else
          {
            allOK = false;
            break;
          }

        if (allOK && (count % 2) == 0)
          result = createInterval(littleZero, littleZero);
        if (allOK && (count % 2) == 1)
          result = createInterval(littleOne, littleOne);

        break;
      }

      case BVAND: // OVER-APPROXIMATION
      {
        if (knownC0 || knownC1)
        {
          if (!knownC1)
          {
            result = createInterval(getEmptyCBV(width), children[0]->maxV);
          }
          else if (!knownC0)
          {
            result = createInterval(getEmptyCBV(width), children[1]->maxV);
          }
          else
          {
            if (CONSTANTBV::BitVector_Lexicompare(children[0]->maxV,
                                                  children[1]->maxV) > 0)
            {
              result = createInterval(getEmptyCBV(width), children[1]->maxV);
            }
            else
              result = createInterval(getEmptyCBV(width), children[0]->maxV);
          }
        }
        break;
      }

      case BVEXTRACT: // OVER-APPROXIMATION
      break;
      {
        if (knownC0) // others are always known..
        {
          unsigned shift_amount = *(children[2]->minV);

          CBV clone = CONSTANTBV::BitVector_Clone(children[0]->maxV);
          while (shift_amount-- > 0)
          {
            CONSTANTBV::BitVector_shift_right(clone, 0);
          }

          //  If the max bit of clone is greater than the width, ok to continue.
          if (CONSTANTBV::Set_Max(clone) < width)
          {
            CBV max = getEmptyCBV(width); // new width.
            for (unsigned i = 0; i < width; i++)
              if (CONSTANTBV::BitVector_bit_test(clone, i))
                CONSTANTBV::BitVector_Bit_On(max, i);

            result = createInterval(getEmptyCBV(width), max);
          }

          CONSTANTBV::BitVector_Destroy(clone);
        }
        break;
      }

      case BVRIGHTSHIFT:
        if (knownC0 || knownC1)
        {
          result = freshUnsignedInterval(width);

          const UnsignedInterval* c0 = children[0];
          const UnsignedInterval* c1 = children[1];

          // The maximum result is the maximum >> (minimum shift).
          if (CONSTANTBV::Set_Max(c1->minV) > 1 + std::log2(width) ||
              *(c1->minV) > width)
          {
            // The maximum is zero.
            CONSTANTBV::BitVector_Flip(result->maxV);
          }
          else
          {
            unsigned shift_amount = *(c1->minV);
            CONSTANTBV::BitVector_Copy(result->maxV, c0->maxV);
            while (shift_amount-- > 0)
            {
              CONSTANTBV::BitVector_shift_right(result->maxV, 0);
            }
          }

          // The minimum result is the minimum >> (maximum shift).
          if (CONSTANTBV::Set_Max(c1->maxV) > 1 + std::log2(width) ||
              *(c1->maxV) > width)
          {
            // The mimimum is zero. (which it's set to by default.).
          }
          else
          {
            unsigned shift_amount = *(c1->maxV);
            CONSTANTBV::BitVector_Copy(result->minV, c0->minV);
            while (shift_amount-- > 0)
              CONSTANTBV::BitVector_shift_right(result->minV, 0);
          }
        }
        break;

      case BVPLUS:
        if (knownC0 && knownC1)
        {
          //  >=2 arity.
          result = freshUnsignedInterval(width);
          CONSTANTBV::BitVector_Flip(result->maxV); // make the max zero too.

          bool min_carry;
          bool max_carry;

          for (size_t i = 0; i < children.size(); i++)
          {
            if (children[i]->isComplete())
            {
              delete result;
              result = nullptr;
              break;
            }

            max_carry = false;
            min_carry = false;

            CONSTANTBV::BitVector_add(result->maxV, result->maxV,
                                      children[i]->maxV, &max_carry);
            CONSTANTBV::BitVector_add(result->minV, result->minV,
                                      children[i]->minV, &min_carry);
            if (min_carry != max_carry)
            {
              delete result;
              result = nullptr;
              break;
            }
          }
        }
        break;

      case BVCONCAT:
        if ((knownC0 || knownC1))
        {
          const UnsignedInterval* c0 = children[0];
          const UnsignedInterval* c1 = children[1];

          CBV min = CONSTANTBV::BitVector_Concat(c0->minV, c1->minV);
          CBV max = CONSTANTBV::BitVector_Concat(c0->maxV, c1->maxV);

          result = createInterval(min, max);

          CONSTANTBV::BitVector_Destroy(min);
          CONSTANTBV::BitVector_Destroy(max);
        }
        break;

      // TODO
      case BVXOR:
      case BVOR:
      case SBVDIV:
      case SBVREM:
      case BVLEFTSHIFT:
      case BVSRSHIFT:
      case SBVMOD:
      default:
        propagatorNotImplemented++;
        break;
    }

    if (result != NULL && result->isComplete())
    {
      delete result;
      result = NULL;
    }

    if (result != NULL)
    {
      result->checkUnsignedInvariant();
    }

    return result;
  }

  UnsignedInterval* UnsignedIntervalAnalysis::visit(const ASTNode& n,
                          NodeToUnsignedIntervalMap& visited)
  {
    {
      NodeToUnsignedIntervalMap::iterator it;
      if ((it = visited.find(n)) != visited.end())
        return it->second;
    }

    if (n.GetKind() == SYMBOL || n.GetKind() == WRITE || n.GetKind() == READ)
      return NULL; // Never know anything about these.

    const auto number_children = n.Degree();
    vector<const UnsignedInterval*> children;

    children.reserve(number_children);

    for (unsigned i = 0; i < number_children; i++)
    {
      UnsignedInterval* r = visit(n[i], visited);
      if (r != NULL)
      {
        assert(!r->isComplete());
      }
      children.push_back(r);
    }

    UnsignedInterval* result = dispatchToTransferFunctions(n,children);

    // result will often be null (which we take to mean the maximum range).
    visited.insert({n, result});
    return result;
  }

  UnsignedIntervalAnalysis::UnsignedIntervalAnalysis(STPMgr& _bm) : bm(_bm)
  {
    littleZero = getEmptyCBV(1);
    littleOne = CONSTANTBV::BitVector_Create(1, true);
    CONSTANTBV::BitVector_Fill(littleOne);
  }

  UnsignedIntervalAnalysis::~UnsignedIntervalAnalysis()
  {
    for (auto it : emptyIntervals)
      if (it.second != NULL)
        delete it.second;

    for (auto it : emptyCBV)
      if (it.second != NULL)
        CONSTANTBV::BitVector_Destroy(it.second);

    CONSTANTBV::BitVector_Destroy(littleOne);
  }
}

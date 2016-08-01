// -*- c++ -*-
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

#ifndef UNSIGNEDINTERVALANALYSIS_H_
#define UNSIGNEDINTERVALANALYSIS_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/StrengthReduction.h"

#ifdef _MSC_VER
#include <compdep.h>
#endif

#include <iostream>

namespace stp
{
using std::make_pair;

class UnsignedIntervalAnalysis // not copyable
{

  vector<UnsignedInterval*> toDeleteLater;
  vector<CBV> likeAutoPtr;

  UnsignedInterval* freshUnsignedInterval(int width)
  {
    assert(width > 0);
    UnsignedInterval* it = createInterval(makeCBV(width), makeCBV(width));
    CONSTANTBV::BitVector_Fill(it->maxV);
    return it;
  }

  // We create all intervals through here. Handles collection
  UnsignedInterval* createInterval(CBV min, CBV max)
  {
    UnsignedInterval* it = new UnsignedInterval(min, max);
    toDeleteLater.push_back(it);
    return it;
  }

  CBV makeCBV(int width)
  {
    CBV result = CONSTANTBV::BitVector_Create(width, true);
    likeAutoPtr.push_back(result);
    return result;
  }

public:

  // Replace some of the things that unsigned intervals can figure out for us.
  ASTNode topLevel_unsignedIntervals(const ASTNode& top)
  {
    bm.GetRunTimes()->start(RunTimes::IntervalPropagation);
    map<const ASTNode, UnsignedInterval*> visited;
    visit(top, visited);
    bm.GetRunTimes()->stop(RunTimes::IntervalPropagation);

    StrengthReduction sr(bm);
    return sr.topLevel(top,visited);
  }

private:
  UnsignedInterval* visit(const ASTNode& n,
                      map<const ASTNode, UnsignedInterval*>& visited)
  {
    map<const ASTNode, UnsignedInterval*>::iterator it;
    if ((it = visited.find(n)) != visited.end())
      return it->second;

    const int number_children = n.Degree();
    vector<UnsignedInterval*> children;
    children.reserve(number_children);
    for (int i = 0; i < number_children; i++)
    {
      children.push_back(visit(n[i], visited));
    }

    UnsignedInterval* result = NULL;
    const unsigned int width = n.GetValueWidth();
    const bool knownC0 = number_children < 1 ? false : (children[0] != NULL);
    const bool knownC1 = number_children < 2 ? false : (children[1] != NULL);

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
        }
        break;
      case BVGT:
      case BVSGT: // OVER-APPROXIMATION
        if ((BVGT == n.GetKind() && knownC0 && knownC1) ||
            (BVSGT == n.GetKind() && knownC0 && knownC1 &&
             !CONSTANTBV::BitVector_bit_test(children[0]->maxV,
                                             n[0].GetValueWidth() - 1) &&
             !CONSTANTBV::BitVector_bit_test(children[1]->maxV,
                                             n[0].GetValueWidth() - 1)))
        {
          if (CONSTANTBV::BitVector_Lexicompare(children[0]->minV,
                                                children[1]->maxV) > 0)
            result = createInterval(littleOne, littleOne);

          if (CONSTANTBV::BitVector_Lexicompare(children[1]->minV,
                                                children[0]->maxV) >= 0)
            result = createInterval(littleZero, littleZero);
        }
        break;
      case BVGE:
      case BVSGE: // OVER-APPROXIMATION
        if ((BVGE == n.GetKind() && knownC0 && knownC1) ||
            (BVSGE == n.GetKind() && knownC0 && knownC1 &&
             !CONSTANTBV::BitVector_bit_test(children[0]->maxV,
                                             n[0].GetValueWidth() - 1) &&
             !CONSTANTBV::BitVector_bit_test(children[1]->maxV,
                                             n[0].GetValueWidth() - 1)))
        {
          if (CONSTANTBV::BitVector_Lexicompare(children[0]->minV,
                                                children[1]->maxV) >= 0)
            result = createInterval(littleOne, littleOne);
          if (CONSTANTBV::BitVector_Lexicompare(children[1]->minV,
                                                children[0]->maxV) > 0)
            result = createInterval(littleZero, littleZero);
        }
        break;
      case BVDIV: // OVER-APPROXIMATION
        if (knownC1)
        {
          // When we're dividing by zero, we know nothing.
          if (!CONSTANTBV::BitVector_is_empty(children[1]->minV))
          {
            UnsignedInterval* top = (children[0] == NULL)
                                    ? freshUnsignedInterval(width)
                                    : children[0];
            result = freshUnsignedInterval(width);

            CBV remainder = CONSTANTBV::BitVector_Create(width, true);

            CBV tmp0 = CONSTANTBV::BitVector_Clone(top->minV);
            CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(
                result->minV, tmp0, children[1]->maxV, remainder);
            assert(0 == e);
            CONSTANTBV::BitVector_Destroy(tmp0);

            tmp0 = CONSTANTBV::BitVector_Clone(top->maxV);
            e = CONSTANTBV::BitVector_Div_Pos(result->maxV, tmp0,
                                              children[1]->minV, remainder);
            assert(0 == e);

            CONSTANTBV::BitVector_Destroy(tmp0);
            CONSTANTBV::BitVector_Destroy(remainder);
          }
        }
        break;
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
        if (knownC0 && knownC1)
        {
          // If the maximum doesn't have the top bit set, then zero extend it.
          if (!CONSTANTBV::BitVector_bit_test(children[0]->maxV,
                                              n[0].GetValueWidth() - 1))
          {
            result = freshUnsignedInterval(n.GetValueWidth());

            // Copy in the minimum and maximum.
            for (unsigned i = 0; i < n[0].GetValueWidth(); i++)
            {
              if (CONSTANTBV::BitVector_bit_test(children[0]->maxV, i))
                CONSTANTBV::BitVector_Bit_On(result->maxV, i);
              else
                CONSTANTBV::BitVector_Bit_Off(result->maxV, i);

              if (CONSTANTBV::BitVector_bit_test(children[0]->minV, i))
                CONSTANTBV::BitVector_Bit_On(result->minV, i);
              else
                CONSTANTBV::BitVector_Bit_Off(result->minV, i);
            }

            for (unsigned i = n[0].GetValueWidth(); i < n.GetValueWidth(); i++)
              CONSTANTBV::BitVector_Bit_Off(result->maxV, i);
          }
        }
        break;
      case BVNEG:
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
        }
        break;
      case ITE:
        if (children[1] != NULL && children[2] != NULL)
        {
          // Both terms and propositions.
          result = freshUnsignedInterval(width == 0 ? 1 : width);
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
            result = NULL;
        }
        break;
        // case BVLEFTSHIFT:
        // case BVAND:
        // case BVSRSHIFT:
        //{
          // Todo two cases.
          // 1) The maximum shift of the maximum value doesn't overflow, and,
          // 2) The minimum shift of the minimum value completely overflows (to
          // zero).
        //}

      case BVRIGHTSHIFT: //OVER-APPROXIMATION
        if (knownC0 || knownC1)
        {
          result = freshUnsignedInterval(width);

          if (children[0] == NULL)
            children[0] = freshUnsignedInterval(width);
          if (children[1] == NULL)
            children[1] = freshUnsignedInterval(width);

          // The maximum result is the maximum >> (minimum shift).
          if (CONSTANTBV::Set_Max(children[1]->minV) > 1 + log2(width) ||
              *(children[1]->minV) > width)
          {
            // The maximum is zero.
            CONSTANTBV::BitVector_Flip(result->maxV);
          }
          else
          {
            unsigned shift_amount = *(children[1]->minV);
            CONSTANTBV::BitVector_Copy(result->maxV, children[0]->maxV);
            while (shift_amount-- > 0)
            {
              CONSTANTBV::BitVector_shift_right(result->maxV, 0);
            }
          }

          // The minimum result is the minimum >> (maximum shift).
          if (CONSTANTBV::Set_Max(children[1]->maxV) > 1 + log2(width) ||
              *(children[1]->maxV) > width)
          {
            // The mimimum is zero. (which it's set to by default.).
          }
          else
          {
            unsigned shift_amount = *(children[1]->maxV);
            CONSTANTBV::BitVector_Copy(result->minV, children[0]->minV);
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

          bool min_carry = false;
          bool max_carry = false;

          for (size_t i = 0; i < children.size(); i++)
          {
            if (children[i] == NULL)
            {
              result = NULL;
              break;
            }

            CONSTANTBV::BitVector_add(result->maxV, result->maxV,
                                      children[i]->maxV, &max_carry);
            CONSTANTBV::BitVector_add(result->minV, result->minV,
                                      children[i]->minV, &min_carry);
            if (min_carry != max_carry)
            {
              result = NULL;
              break;
            }
          }

        }
        break;
      case BVCONCAT:
        if ((knownC0 || knownC1))
        {
          result = freshUnsignedInterval(n.GetValueWidth());

          // Copy in the lower part.
          if (knownC1)
          {
            // Copy in the minimum and maximum.
            for (unsigned i = 0; i < n[1].GetValueWidth(); i++)
            {
              if (CONSTANTBV::BitVector_bit_test(children[1]->maxV, i))
                CONSTANTBV::BitVector_Bit_On(result->maxV, i);
              else
                CONSTANTBV::BitVector_Bit_Off(result->maxV, i);

              if (CONSTANTBV::BitVector_bit_test(children[1]->minV, i))
                CONSTANTBV::BitVector_Bit_On(result->minV, i);
              else
                CONSTANTBV::BitVector_Bit_Off(result->minV, i);
            }
          }

          if (knownC0)
          {
            // Copy in the minimum and maximum.
            for (unsigned i = n[1].GetValueWidth(); i < n.GetValueWidth(); i++)
            {
              if (CONSTANTBV::BitVector_bit_test(children[0]->maxV,
                                                 i - n[1].GetValueWidth()))
                CONSTANTBV::BitVector_Bit_On(result->maxV, i);
              else
                CONSTANTBV::BitVector_Bit_Off(result->maxV, i);

              if (CONSTANTBV::BitVector_bit_test(children[0]->minV,
                                                 i - n[1].GetValueWidth()))
                CONSTANTBV::BitVector_Bit_On(result->minV, i);
              else
                CONSTANTBV::BitVector_Bit_Off(result->minV, i);
            }
          }
        }
        break;
      default:
      {
        // Debugging!

        bool nonNull = true;
        // If all the children are known, output 'em.
        for (size_t i = 0; i < n.Degree(); i++)
        {
          if (children[i] == NULL)
            nonNull = false;
        }

        if (false && nonNull && n.GetKind() != SYMBOL && n.GetKind() != AND)
        {
          std::cerr << n;
          for (size_t i = 0; i < n.Degree(); i++)
            children[i]->print();
        }
      }
    }

    if (result != NULL && result->isComplete())
      result = NULL;

    if (result != NULL)
      result->checkUnsignedInvariant();

    // result will often be null (which we take to mean the maximum range).
    visited.insert(make_pair(n, result));
    return result;
  }

  STPMgr& bm;
  CBV littleOne;
  CBV littleZero;
  NodeFactory* nf;

public:
  UnsignedIntervalAnalysis(STPMgr& _bm) : bm(_bm)
  {
    littleZero = makeCBV(1);
    littleOne = makeCBV(1);
    CONSTANTBV::BitVector_Fill(littleOne);
    nf = bm.defaultNodeFactory;
  }

  ~UnsignedIntervalAnalysis()
  {
    for (size_t i = 0; i < toDeleteLater.size(); i++)
      delete toDeleteLater[i];

    for (size_t i = 0; i < likeAutoPtr.size(); i++)
      CONSTANTBV::BitVector_Destroy(likeAutoPtr[i]);

    likeAutoPtr.clear();
    toDeleteLater.clear();
  }
};
}

#endif

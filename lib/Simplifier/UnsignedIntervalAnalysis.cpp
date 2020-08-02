/********************************************************************
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
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include <iostream>
#include <map>
#include <cmath>

using std::map;

namespace stp
{
  void UnsignedIntervalAnalysis::print_stats()
  {
    std::cerr << "{UnsignedIntervalAnalysis} TODO propagator not implemented: "
              << propagatorNotImplemented << std::endl;
    std::cerr << "{UnsignedIntervalAnalysis} Iterations: " << iterations
              << std::endl;
  }


  using std::make_pair;

  UnsignedInterval* UnsignedIntervalAnalysis::freshUnsignedInterval(int width)
  {
    assert(width > 0);
    UnsignedInterval* it = createInterval(makeCBV(width), makeCBV(width));
    CONSTANTBV::BitVector_Fill(it->maxV);
    return it;
  }

  // We create all intervals through here. Handles collection
  UnsignedInterval* UnsignedIntervalAnalysis::createInterval(CBV min, CBV max)
  {
    UnsignedInterval* it = new UnsignedInterval(min, max);
    toDeleteLater.push_back(it);
    return it;
  }

  CBV UnsignedIntervalAnalysis::makeCBV(int width)
  {
    CBV result = CONSTANTBV::BitVector_Create(width, true);
    likeAutoPtr.push_back(result);
    return result;
  }

  // Replace some of the things that unsigned intervals can figure out for us.
  ASTNode UnsignedIntervalAnalysis::topLevel_unsignedIntervals(const ASTNode& top)
  {
    propagatorNotImplemented = 0;

    bm.GetRunTimes()->start(RunTimes::IntervalPropagation);
    map<const ASTNode, UnsignedInterval*> visited;
    visit(top, visited);
    bm.GetRunTimes()->stop(RunTimes::IntervalPropagation);

    StrengthReduction sr(bm);
    ASTNode r = sr.topLevel(top, visited);

    if (bm.UserFlags.stats_flag)
    {
      print_stats();
      sr.stats("UnsignedIntervalAnalysis");
    }

    return r;
  }

  UnsignedInterval* UnsignedIntervalAnalysis::visit(const ASTNode& n,
                          map<const ASTNode, UnsignedInterval*>& visited)
  {
    map<const ASTNode, UnsignedInterval*>::iterator it;
    if ((it = visited.find(n)) != visited.end())
      return it->second;

    if (n.GetKind() == SYMBOL || n.GetKind() == WRITE || n.GetKind() == READ)
      return NULL; // Never know anything about these.

    const int number_children = n.Degree();
    vector<UnsignedInterval*> children;
    vector<bool> known;

    children.reserve(number_children);
    known.reserve(number_children);

    for (int i = 0; i < number_children; i++)
    {
      UnsignedInterval* r = visit(n[i], visited);
      if (r != NULL)
      {
        assert(!r->isComplete());
      }
      known.push_back(r != NULL);
      children.push_back(r);
    }

    UnsignedInterval* result = NULL;
    const unsigned int width = n.GetValueWidth();
    const bool knownC0 = number_children < 1 ? false : (children[0] != NULL);
    const bool knownC1 = number_children < 2 ? false : (children[1] != NULL);

    iterations++;

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
      case BVSGT: // OVER-APPROXIMATION
        if (knownC1 || knownC0)
        {
          const unsigned bitwidth = n[0].GetValueWidth();

          UnsignedInterval c0 =
              knownC0 ? *children[0] : *freshUnsignedInterval(bitwidth);
          UnsignedInterval c1 =
              knownC1 ? *children[1] : *freshUnsignedInterval(bitwidth);

          if (CONSTANTBV::BitVector_Lexicompare(c0.minV, c1.maxV) > 0)
            result = createInterval(littleOne, littleOne);

          if (CONSTANTBV::BitVector_Lexicompare(c1.minV, c0.maxV) >= 0)
            result = createInterval(littleZero, littleZero);

          if (BVSGT == n.GetKind() && result != NULL)
          {
            bool c0Min = CONSTANTBV::BitVector_bit_test(c0.minV, bitwidth - 1);
            bool c0Max = CONSTANTBV::BitVector_bit_test(c0.maxV, bitwidth - 1);

            bool c1Min = CONSTANTBV::BitVector_bit_test(c1.minV, bitwidth - 1);
            bool c1Max = CONSTANTBV::BitVector_bit_test(c1.maxV, bitwidth - 1);

            // BVGT xor MSB xor MSB
            if ((c0Min == c0Max) && (c1Min == c1Max))
            {
              assert(result->isConstant());

              if ((c0Min != c1Min) !=
                  CONSTANTBV::BitVector_bit_test(result->minV, 0))
                result = createInterval(littleOne, littleOne);
              else
                result = createInterval(littleZero, littleZero);

              //              std::cerr << c0Min << c1Min << CONSTANTBV::BitVector_bit_test(result->minV,0) << std::endl;
            }
            else
              result = freshUnsignedInterval(1);
          }
        }
        break;

      case BVDIV:
      {
        UnsignedInterval* c1;
        if (!knownC1)
        {
          c1 = freshUnsignedInterval(width);
        }
        else
          c1 = children[1];

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

        UnsignedInterval* top =
            (children[0] == NULL) ? freshUnsignedInterval(width) : children[0];
        result = freshUnsignedInterval(width);

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
        if (children[0] != NULL)
        {
          assert(children[0]->isConstant());
          result = freshUnsignedInterval(width == 0 ? 1 : width);
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
        else if (children[1] != NULL && children[2] != NULL)
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

      case AND:
      {
        // If any are definately zero then the answer is zero.
        for (unsigned i = 0; i < children.size(); i++)
          if (children[i] != NULL &&
              (CONSTANTBV::BitVector_is_empty(children[i]->maxV)))
          {
            result = createInterval(littleZero, littleZero);
            break;
          }
        // If all are definately one the answer is one.
        bool allok = true;
        for (unsigned i = 0; i < children.size(); i++)
          if (children[i] == NULL ||
              (CONSTANTBV::BitVector_is_empty(children[i]->minV)))
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
          if (children[i] != NULL &&
              (CONSTANTBV::BitVector_is_full(children[i]->minV)))
          {
            result = createInterval(littleOne, littleOne);
            break;
          }
        // If all are definately false the answer is false.
        bool allfalse = true;
        for (unsigned i = 0; i < children.size(); i++)
          if (children[i] == NULL ||
              (CONSTANTBV::BitVector_is_full(children[i]->maxV)))
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
          if (children[i] != NULL && children[i]->isConstant())
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
            result = createInterval(makeCBV(width), children[0]->maxV);
          }
          else if (!knownC0)
          {
            result = createInterval(makeCBV(width), children[1]->maxV);
          }
          else
          {
            if (CONSTANTBV::BitVector_Lexicompare(children[0]->maxV,
                                                  children[1]->maxV) > 0)
            {
              result = createInterval(makeCBV(width), children[1]->maxV);
            }
            else
              result = createInterval(makeCBV(width), children[0]->maxV);
          }
        }
        break;
      }

      case BVEXTRACT: // OVER-APPROXIMATION
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
            CBV max = makeCBV(width); // new width.
            for (unsigned i = 0; i < width; i++)
              if (CONSTANTBV::BitVector_bit_test(clone, i))
                CONSTANTBV::BitVector_Bit_On(max, i);

            result = createInterval(makeCBV(width), max);
          }

          CONSTANTBV::BitVector_Destroy(clone);
        }
        break;
      }

      case BVRIGHTSHIFT: //OVER-APPROXIMATION
        if (knownC0 || knownC1)
        {
          result = freshUnsignedInterval(width);

          if (children[0] == NULL)
            children[0] = freshUnsignedInterval(width);
          if (children[1] == NULL)
            children[1] = freshUnsignedInterval(width);

          // The maximum result is the maximum >> (minimum shift).
          if (CONSTANTBV::Set_Max(children[1]->minV) > 1 + std::log2(width) ||
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
          if (CONSTANTBV::Set_Max(children[1]->maxV) > 1 + std::log2(width) ||
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

          bool min_carry;
          bool max_carry;

          for (size_t i = 0; i < children.size(); i++)
          {
            if (children[i] == NULL)
            {
              result = NULL;
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
              result = NULL;
              break;
            }
          }
        }
        break;

      case BVCONCAT:
        if ((knownC0 || knownC1))
        {
          UnsignedInterval* c0 =
              knownC0 ? children[0]
                      : freshUnsignedInterval(n[0].GetValueWidth());
          UnsignedInterval* c1 =
              knownC1 ? children[1]
                      : freshUnsignedInterval(n[1].GetValueWidth());

          CBV min = CONSTANTBV::BitVector_Concat(c0->minV, c1->minV);
          CBV max = CONSTANTBV::BitVector_Concat(c0->maxV, c1->maxV);

          likeAutoPtr.push_back(min);
          likeAutoPtr.push_back(max);

          result = createInterval(min, max);
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
      result = NULL;

    if (result != NULL)
    {
      result->checkUnsignedInvariant();
    }

    // result will often be null (which we take to mean the maximum range).
    visited.insert(make_pair(n, result));
    return result;
  }


  UnsignedIntervalAnalysis::UnsignedIntervalAnalysis(STPMgr& _bm) : bm(_bm)
  {
    littleZero = makeCBV(1);
    littleOne = makeCBV(1);
    CONSTANTBV::BitVector_Fill(littleOne);
    nf = bm.defaultNodeFactory;
  }

  UnsignedIntervalAnalysis::~UnsignedIntervalAnalysis()
  {
    for (size_t i = 0; i < toDeleteLater.size(); i++)
      delete toDeleteLater[i];

    for (size_t i = 0; i < likeAutoPtr.size(); i++)
      CONSTANTBV::BitVector_Destroy(likeAutoPtr[i]);

    likeAutoPtr.clear();
    toDeleteLater.clear();
  }

}



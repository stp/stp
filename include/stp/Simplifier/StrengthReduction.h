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
 *  Takes the result of an analysis and uses it to simplify, for example,
 *  if both operands of a signed division have the same MSB, it can be converted
 *  to an unsigned division, instead.
 */

#ifndef STRENGTHREDUCTION_H_
#define STRENGTHREDUCTION_H_

#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <map>

#ifdef _MSC_VER
#include <compdep.h>
#endif

#include <iostream>

namespace stp
{
using std::make_pair;
using simplifier::constantBitP::FixedBits;

class StrengthReduction // not copyable
{
  unsigned replaceWithConstant;
  unsigned replaceWithSimpler;
  unsigned unimplementedReduction;

  // A special version that handles the lhs appearing in the rhs of the fromTo
  // map.
  ASTNode replace(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& cache)
  {
    if (n.isAtom())
      return n;

    if (cache.find(n) != cache.end())
      return (*(cache.find(n))).second;

    ASTNode result = n;

    if (fromTo.find(n) != fromTo.end())
    {
      result = (*fromTo.find(n)).second;
      fromTo.erase(n); // this is how it differs from the everyday replace.
    }

    ASTVec new_children;
    new_children.reserve(result.GetChildren().size());

    for (size_t i = 0; i < result.Degree(); i++)
      new_children.push_back(replace(result[i], fromTo, cache));

    if (new_children == result.GetChildren())
    {
      cache.insert(make_pair(n, result));
      return result;
    }

    if (n.GetValueWidth() == 0) // n.GetType() == BOOLEAN_TYPE
    {
      result = nf->CreateNode(result.GetKind(), new_children);
    }
    else
    {
      // If the index and value width aren't saved, they are reset sometimes
      // (??)
      result = nf->CreateArrayTerm(result.GetKind(), result.GetIndexWidth(),
                                   result.GetValueWidth(), new_children);
    }

    cache.insert(make_pair(n, result));
    return result;
  }

public:

  //TODO merge these two toplevel funtions, they do the same thing..
  ASTNode topLevel(const ASTNode& top, const std::map<ASTNode, FixedBits*>& visited)
  {
    ASTNodeMap fromTo;

    for (auto it = visited.begin(); it != visited.end(); it++)
    {
      const ASTNode& n = it->first;
      if (n.isConstant())
        continue;

      const Kind kind = n.GetKind();
      const FixedBits* b = it->second;
      
      if (b!= NULL && b->isTotallyFixed()) // Replace with a constant.
      { 
        ASTNode newN;
        if (n.GetType() == BOOLEAN_TYPE)
        {
          if (b->getValue(0)) // true
            newN = nf->getTrue();
          else
            newN = nf->getFalse();
        }
        else
          newN = nf->CreateConstant(b->GetBVConst(), n.GetValueWidth());

        fromTo.insert(std::make_pair(n,newN));
        replaceWithConstant++;
      }
      else if (kind == BVSGT || kind == SBVDIV || kind == SBVMOD || kind == SBVREM)
      {
        if (visited.find(n[0]) != visited.end() && visited.find(n[1]) != visited.end())
         if (visited.find(n[0])->second != NULL && visited.find(n[1])->second != NULL)
          {
             const FixedBits * l =  visited.find(n[0])->second;
             const FixedBits * r =  visited.find(n[1])->second;
             const unsigned bw = n[0].GetValueWidth();
             if (l->isFixed(bw-1) && r->isFixed(bw-1))
              {
                if (kind == BVSGT && (l->getValue(bw-1) == r->getValue(bw-1)))
                {
                  // replace with unsigned comparison.
                  ASTNode newN = nf->CreateNode(BVGT, n[0], n[1]);
                  fromTo.insert(make_pair(n, newN));
                  replaceWithSimpler++;
                  //std::cerr << n << *l << *r << newN << std::endl;
                }
                else if (kind == SBVDIV)
                {
                  unimplementedReduction++; 
                }
                else if (kind == SBVMOD)
                {
                  unimplementedReduction++; 
                }
                else if (kind == SBVREM)
                {
                  unimplementedReduction++; 
                }
              }
          }
      }
      else if (kind == BVPLUS || kind == BVXOR)
      {
        // If all the bits are zero except for one, in each position, replace by OR
        vector<FixedBits*> children;
        bool bad=false;
        for (ASTNode c: n.GetChildren())
        {
          if (visited.find(c) == visited.end())
            bad = true;
          children.push_back(visited.find(c)->second);
          if (children.back() == NULL)
            bad=true;
        }
        if(!bad)
        {
          unsigned nonZero = 0;
          for (unsigned i =0; i < n.GetValueWidth();i++)
          {
            nonZero =0;
            for (unsigned j =0; j < children.size(); j++)
            {
              if (!children[j]->isFixed(i))
                nonZero++;
              else if (children[j]->getValue(i))
                nonZero++;
            }
            if (nonZero > 1)  
              break;
          }
          
          if (nonZero <=1) // OK can reduce.
          {
            ASTNode newN= nf->CreateTerm(BVOR, n.GetValueWidth(), n.GetChildren());
            replaceWithSimpler++;
            fromTo.insert(make_pair(n, newN));
          }
        }
      }
      else if (b!= NULL)
      {
        if (kind== BVSRSHIFT && b->isFixed(n.GetValueWidth()-1) && !b->getValue(n.GetValueWidth()-1) )
        {
          // Reduce from signed right shift, to ordinary right shift.
          ASTNode newN = nf->CreateTerm(BVRIGHTSHIFT, n.GetValueWidth(), n[0], n[1]);
          fromTo.insert(make_pair(n, newN));
          replaceWithSimpler++;
        }
        else if (n.GetKind() == BVSX && b->isFixed(n.GetValueWidth()-1) && n[0].GetValueWidth() != n.GetValueWidth())
        {
          // We can replace the BVSX with a concat.
          ASTNode concat;
          if (b->getValue(n.GetValueWidth()-1))
            concat = bm.CreateMaxConst(n.GetValueWidth() - n[0].GetValueWidth());
          else
            concat = bm.CreateZeroConst(n.GetValueWidth() - n[0].GetValueWidth());

          ASTNode newN = nf->CreateTerm(BVCONCAT, n.GetValueWidth(),concat, n[0]);
          fromTo.insert(make_pair(n, newN));
          replaceWithSimpler++;
        }
      }
    }

    //stats();

    if (fromTo.size() == 0)
      return top;

    ASTNodeMap cache;
    return SubstitutionMap::replace(top, fromTo, cache, nf);
  }

  // Replace some of the things that unsigned intervals can figure out for us.
  // Reduce from signed to unsigned if possible.
  ASTNode topLevel(const ASTNode& top, const std::map<const ASTNode, UnsignedInterval*>& visited)
  {
    ASTNodeMap fromTo;
    ASTNodeMap onePass;
    for (std::map<const ASTNode, UnsignedInterval*>::const_iterator it = visited.begin();
         it != visited.end(); it++)
    {
      const ASTNode& n = it->first;
      UnsignedInterval* interval = it->second;
      const int width = n.GetValueWidth();

      if (n.isConstant())
        continue;

      const Kind k = n.GetKind();

      // We do this rule if we don't know for certain the result.
      // If the leading bits are false then we can reduce from signed to
      // unsigned comparison.
      if ((interval == NULL || !interval->isConstant()) &&
          (k == BVSGT || k == BVSGE || k == SBVDIV || k == BVSRSHIFT ||
           k == SBVREM || k == BVSX))
      {
        std::map<const ASTNode, UnsignedInterval*>::const_iterator l =
            visited.find(n[0]);
        std::map<const ASTNode, UnsignedInterval*>::const_iterator r =
            visited.find(n[1]);

        bool lhs, rhs; // isFalse.

        if (l == visited.end())
          lhs = false;
        else
        {
          UnsignedInterval* a = (*l).second;
          if (a == NULL)
            lhs = false;
          else
          {
            lhs = !CONSTANTBV::BitVector_bit_test(a->maxV,
                                                  n[0].GetValueWidth() - 1);
          }
        }

        if (r == visited.end())
          rhs = false;
        else
        {
          UnsignedInterval* b = (*r).second;
          if (b == NULL)
            rhs = false;
          else
            rhs = !CONSTANTBV::BitVector_bit_test(b->maxV,
                                                  n[0].GetValueWidth() - 1);
        }

        switch (n.GetKind())
        {
          case BVSGT:
          case BVSGE:
            if (lhs && rhs)
            {
              ASTNode newN = nf->CreateNode(n.GetKind() == BVSGT ? BVGT : BVGE,
                                            n[0], n[1]);
              fromTo.insert(make_pair(n, newN));
            }
            break;

          case SBVDIV:
            if (lhs && rhs)
            {
              ASTNode newN =
                  nf->CreateTerm(BVDIV, n.GetValueWidth(), n[0], n[1]);
              fromTo.insert(make_pair(n, newN));
            }
            break;

          case SBVREM:
            if (lhs && rhs)
            {
              ASTNode newN =
                  nf->CreateTerm(BVMOD, n.GetValueWidth(), n[0], n[1]);
              fromTo.insert(make_pair(n, newN));
            }
            break;

          case BVSRSHIFT:
            if (lhs)
            {
              ASTNode newN =
                  nf->CreateTerm(BVRIGHTSHIFT, n.GetValueWidth(), n[0], n[1]);
              fromTo.insert(make_pair(n, newN));
            }
            break;

          case BVSX:
            if (lhs && n[0].GetValueWidth() != n.GetValueWidth())
            {
              // If it's really a zero extend..
              ASTNode copyN = nf->CreateTerm(
                  BVCONCAT, n.GetValueWidth(),
                  bm.CreateZeroConst(n.GetValueWidth() - n[0].GetValueWidth()),
                  n[0]);
              fromTo.insert(make_pair(n, copyN));
            }
            break;
          default:
            FatalError("Never here");
        }
      }
      if (interval == NULL)
        continue;
      if (interval->isConstant() && n.GetType() == BOOLEAN_TYPE)
      {
        if (0 == CONSTANTBV::BitVector_Lexicompare(interval->maxV, littleOne))
          fromTo.insert(make_pair(n, bm.ASTTrue));
        else
          fromTo.insert(make_pair(n, bm.ASTFalse));
      }
      else if (interval->isConstant() && n.GetType() == BITVECTOR_TYPE)
      {
        CBV clone = CONSTANTBV::BitVector_Clone(interval->maxV);
        ASTNode new_const = bm.CreateBVConst(clone, n.GetValueWidth());
        fromTo.insert(make_pair(n, new_const));
      }
      else if (false && n.GetType() == BITVECTOR_TYPE &&
               n.GetKind() != SYMBOL && n.GetKind() != BVCONCAT)
      {
        // Looks for leading or trailing zeroes/ones, and replaces the node with
        // a
        // concat and an extract.

        // This slows things down. I suspect because the extracts are
        // "simplified" and split too many things.
        bool leadingValue =
            CONSTANTBV::BitVector_bit_test(interval->maxV, width - 1);
        int leadingSame = 0;
        for (int i = width - 1; i >= 0; i--)
        {
          if (CONSTANTBV::BitVector_bit_test(interval->maxV, i) ^ leadingValue)
            break;

          if (CONSTANTBV::BitVector_bit_test(interval->minV, i) ^ leadingValue)
            break;
          leadingSame++;
        }

        assert(leadingSame != width); // That'd be a constant (another case).

        if (leadingSame > 0)
        {
          ASTNode prefix;
          if (leadingValue)
            prefix = bm.CreateMaxConst(leadingSame);
          else
            prefix = bm.CreateZeroConst(leadingSame);

          ASTNode top = bm.CreateBVConst(32, width - leadingSame - 1);
          ASTNode bottom = bm.CreateZeroConst(32);
          ASTNode remainder =
              nf->CreateTerm(BVEXTRACT, width - leadingSame, n, top, bottom);
          ASTNode replaced = nf->CreateTerm(BVCONCAT, width, prefix, remainder);
          onePass.insert(make_pair(n, replaced));
        }
      }
    }

    ASTNode result = top;
    if (onePass.size() > 0)
    {
      // The rhs of the map contains the lhs, so it needs to be applied
      // specially.
      ASTNodeMap cache;
      result = replace(top, onePass, cache);
    }

    if (fromTo.size() > 0)
    {
      ASTNodeMap cache;
      return SubstitutionMap::replace(result, fromTo, cache,nf);
    }

    return result;
  }

private:

  STPMgr& bm;
  CBV littleOne;
  CBV littleZero;
  NodeFactory* nf;

public:
  StrengthReduction(STPMgr& _bm) : bm(_bm)
  {
    littleOne = CONSTANTBV::BitVector_Create(1, true);
    littleZero = CONSTANTBV::BitVector_Create(1, true);
    CONSTANTBV::BitVector_Fill(littleOne);
    nf = bm.defaultNodeFactory;

    replaceWithConstant=0;
    replaceWithSimpler=0;
    unimplementedReduction=0;
  }

  ~StrengthReduction()
  {
    CONSTANTBV::BitVector_Destroy(littleOne);
    CONSTANTBV::BitVector_Destroy(littleZero);
  }

  void stats()
  {
    std::cerr << "replace with constant: " << replaceWithConstant << std::endl;
    std::cerr << "replace with simpler operation: " << replaceWithSimpler << std::endl;
    std::cerr << "TODO replace with simpler operation: " << unimplementedReduction << std::endl;
    
  }
};
}

#endif

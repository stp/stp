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

#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <iostream>

namespace stp
{
  using std::make_pair;
  using simplifier::constantBitP::FixedBits;

  // A special version that handles the lhs appearing in the rhs of the fromTo
  // map.
  ASTNode StrengthReduction::replace(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& cache)
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

  // visit each node apply strength reductions to it.
  ASTNode StrengthReduction::visit(const ASTNode& n, NodeDomainAnalysis& nda, ASTNodeMap& cache)
  {
    if (n.Degree() == 0 )
      return n;

    if (cache.find(n) != cache.end())
      return cache[n];

    ASTVec children;
    children.reserve(n.Degree());
    
    for (const auto & c: n)
    {
      children.push_back(visit(c,nda,cache));
    }

    ASTNode newN;
    if (n.GetType() == BOOLEAN_TYPE)
      newN = nf->CreateNode(n.GetKind(), children);
    else
      newN = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),n.GetValueWidth(), children);
   
    nda.buildMap(newN);
    newN = strengthReduction(newN, *nda.getCbitMap());

    nda.buildMap(newN);
    newN = strengthReduction(newN, *nda.getIntervalMap());

    nda.buildMap(newN);
    newN = strengthReduction(newN, *nda.getValueSetMap());

    cache.insert({n,newN});
    return newN;
  }

  ASTNode StrengthReduction::topLevel(const ASTNode& top, NodeDomainAnalysis& nda)
  {
    ASTNodeMap fromTo;
    ASTNode result = visit(top, nda, fromTo);
    if (uf->stats_flag)
      stats();
    return result;
  }

  // Lots of these rules are more nicely addressed by the fixedbits.
  // When information is transferred properly between domains, lots can be removed.
  ASTNode StrengthReduction::strengthReduction(const ASTNode& n, const NodeToUnsignedIntervalMap& visited)
  {
    ASTNode newN = n;
    const UnsignedInterval* interval = visited.find(n)->second;
    const Kind k = n.GetKind();

    if (interval != nullptr && interval->isConstant())
    {
      replaceWithConstant++;

      if (n.GetType() == BOOLEAN_TYPE)
      {
        if (0 == CONSTANTBV::BitVector_Lexicompare(interval->maxV, littleOne))
          newN = nf->getTrue();
        else
          newN = nf->getFalse();
      }
      else if (n.GetType() == BITVECTOR_TYPE)
      {
        CBV clone = CONSTANTBV::BitVector_Clone(interval->maxV);
        newN = nf->CreateConstant(clone, n.GetValueWidth());
      }
    }
    else if (k == BVSGT || k == BVSGE || k == SBVDIV || k == BVSRSHIFT || k == SBVREM || k == SBVMOD || k == BVSX)
    {
      // If the leading bits are false then we can reduce from signed to
      // unsigned comparison. This is all expressed more naturally using the 
      // bit domain. So when information is copied between the two domains, we wont
      // require this code - the reductions will be applied by the fixed-bit code.
      const auto l = visited.find(n[0]);
      const auto r = visited.find(n[1]);

      bool lhs, rhs; // true if the most significant bits are zero.

      if (l == visited.end())
        lhs = false;
      else
      {
        UnsignedInterval* a = (*l).second;
        if (a == nullptr)
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
        if (b == nullptr)
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
            newN = nf->CreateNode(n.GetKind() == BVSGT ? BVGT : BVGE,
                                          n[0], n[1]);
          }
          break;

        case SBVDIV:
          if (lhs && rhs)
          {
            newN = nf->CreateTerm(BVDIV, n.GetValueWidth(), n[0], n[1]);
          }
          break;

        case SBVREM:
        case SBVMOD:
          if (lhs && rhs)
          {
            // With both operands non-negative these agree with the
            // unsigned remainder, including remainder by zero, which all
            // three define as the dividend.
            newN = nf->CreateTerm(BVMOD, n.GetValueWidth(), n[0], n[1]);
          }
          break;

        case BVSRSHIFT:
          if (lhs)
          {
            newN = nf->CreateTerm(BVRIGHTSHIFT, n.GetValueWidth(), n[0], n[1]);
          }
          break;

        case BVSX:
          if (lhs && n[0].GetValueWidth() != n.GetValueWidth())
          {
            // If it's really a zero extend..
            newN = nf->CreateTerm(
                BVCONCAT, n.GetValueWidth(),
                nf->CreateZeroConst(n.GetValueWidth() - n[0].GetValueWidth()),
                n[0]);
          }
          break;
        default:
          FatalError("Never here");
      }
    }
    return newN;
  }

  ASTNode StrengthReduction::strengthReduction(const ASTNode& n, const NodeToFixedBitsMap& visited)
  {
    const Kind kind = n.GetKind();
    const FixedBits* b = visited.find(n)->second;
    ASTNode newN = n;

    if (b != nullptr && b->isTotallyFixed()) // Replace with a constant.
    {
      if (n.GetType() == BOOLEAN_TYPE)
      {
        if (b->getValue(0)) // true
          newN = nf->getTrue();
        else
          newN = nf->getFalse();
      }
      else
        newN = nf->CreateConstant(b->GetBVConst(), n.GetValueWidth());

      replaceWithConstant++;
    }
    else if (kind == BVSGT || kind == BVSGE || kind == SBVDIV ||
             kind == SBVMOD || kind == SBVREM)
    {
      if (visited.find(n[0]) != visited.end() &&
          visited.find(n[1]) != visited.end())
        if (visited.find(n[0])->second != nullptr &&
            visited.find(n[1])->second != nullptr)
        {
          const FixedBits* l = visited.find(n[0])->second;
          const FixedBits* r = visited.find(n[1])->second;
          const unsigned bw = n[0].GetValueWidth();
          if (l->isFixed(bw - 1) && r->isFixed(bw - 1))
          {
            if ((kind == BVSGT || kind == BVSGE) &&
                (l->getValue(bw - 1) == r->getValue(bw - 1)))
            {
              // replace with unsigned comparison.
              newN = nf->CreateNode(kind == BVSGT ? BVGT : BVGE, n[0], n[1]);
              replaceWithSimpler++;
            }
            else if (kind == SBVDIV || kind == SBVREM)
            {
              // replace with unsigned division / remainder.
              ASTNode s = n[0];
              ASTNode t = n[1];
              const auto width = n.GetValueWidth();
              
              if (l->getValue(bw - 1))
                s = nf->CreateTerm(stp::BVUMINUS, width, s);
              
              if (r->getValue(bw - 1))
                t = nf->CreateTerm(stp::BVUMINUS, width, t);
              
              if (kind == SBVDIV)
                newN = nf->CreateTerm(BVDIV, width, s, t);
              else
                newN = nf->CreateTerm(BVMOD, width, s, t);
              
              if (SBVDIV == kind && (l->getValue(bw - 1) != r->getValue(bw - 1)))
                  newN = nf->CreateTerm(stp::BVUMINUS, width, newN);
              if (SBVREM == kind && l->getValue(bw - 1))
                  newN = nf->CreateTerm(stp::BVUMINUS, width, newN);

              replaceWithSimpler++;
            }
            else if (kind == SBVMOD)
            {
              // The result of bvsmod takes the divisor's sign, so with
              // both signs fixed it's the unsigned remainder of the
              // magnitudes, moved onto the divisor's side of zero.
              const auto width = n.GetValueWidth();
              const bool sNegative = l->getValue(bw - 1);
              const bool tNegative = r->getValue(bw - 1);

              ASTNode absS = n[0];
              ASTNode absT = n[1];

              if (sNegative)
                absS = nf->CreateTerm(BVUMINUS, width, absS);
              if (tNegative)
                absT = nf->CreateTerm(BVUMINUS, width, absT);

              ASTNode u = nf->CreateTerm(BVMOD, width, absS, absT);

              if (sNegative == tNegative)
              {
                // Same signs: already on the divisor's side. This also
                // covers remainder by zero (only possible with both
                // non-negative), where both operations give the dividend.
                newN = sNegative ? nf->CreateTerm(BVUMINUS, width, u) : u;
              }
              else
              {
                // Different signs: a non-zero remainder is off the
                // divisor's side by exactly one divisor.
                const ASTNode zero = nf->CreateZeroConst(width);
                ASTNode shifted = nf->CreateTerm(
                    BVPLUS, width,
                    sNegative ? nf->CreateTerm(BVUMINUS, width, u) : u, n[1]);
                newN = nf->CreateTerm(ITE, width, nf->CreateNode(EQ, u, zero),
                                      zero, shifted);
              }
              replaceWithSimpler++;
            }
          }
        }
    }
    else if (kind == BVPLUS || kind == BVXOR)
    {
      // If all the bits are zero except for one, in each position, replace by OR
      vector<FixedBits*> children;
      bool bad = false;
      for (ASTNode c : n.GetChildren())
      {
        if (visited.find(c) == visited.end())
          bad = true;
        children.push_back(visited.find(c)->second);
        if (children.back() == nullptr)
          bad = true;
      }
      if (!bad)
      {
        unsigned nonZero = 0;
        for (unsigned i = 0; i < n.GetValueWidth(); i++)
        {
          nonZero = 0;
          for (unsigned j = 0; j < children.size(); j++)
          {
            if (!children[j]->isFixed(i))
              nonZero++;
            else if (children[j]->getValue(i))
              nonZero++;
          }
          if (nonZero > 1)
            break;
        }

        if (nonZero <= 1) // OK can reduce.
        {
          newN =
              nf->CreateTerm(BVOR, n.GetValueWidth(), n.GetChildren());
          replaceWithSimpler++;
        }
      }
    }
    else if (b != nullptr)
    {
      if (kind == BVSRSHIFT && b->isFixed(n.GetValueWidth() - 1) &&
          !b->getValue(n.GetValueWidth() - 1))
      {
        // Reduce from signed right shift, to ordinary right shift.
        newN =
            nf->CreateTerm(BVRIGHTSHIFT, n.GetValueWidth(), n[0], n[1]);
        replaceWithSimpler++;
      }
      else if (n.GetKind() == BVSX && b->isFixed(n.GetValueWidth() - 1) &&
               n[0].GetValueWidth() != n.GetValueWidth())
      {
        // We can replace the BVSX with a concat.
        ASTNode concat;
        if (b->getValue(n.GetValueWidth() - 1))
          concat =
              nf->CreateMaxConst(n.GetValueWidth() - n[0].GetValueWidth());
        else
          concat =
              nf->CreateZeroConst(n.GetValueWidth() - n[0].GetValueWidth());

        newN =
            nf->CreateTerm(BVCONCAT, n.GetValueWidth(), concat, n[0]);
        replaceWithSimpler++;
      }
    } 
    return newN;
  }

  ASTNode StrengthReduction::strengthReduction(const ASTNode& n, const NodeToValueSetMap& visited)
  {
    // An equality whose sides share exactly one possible value holds
    // just when both sides take that value, so it splits into a
    // conjunction of equalities against a constant - which simplify
    // further (an ITE over constants folds towards its condition, for
    // instance). Disjoint sides don't need handling here; the
    // equality's own domain is then a constant false, which the other
    // passes replace.
    if (n.GetKind() != EQ)
      return n;

    // With a constant on either side the equality already is a
    // comparison against a constant; the split would rebuild it.
    if (n[0].isConstant() || n[1].isConstant())
      return n;

    const auto l = visited.find(n[0]);
    const auto r = visited.find(n[1]);
    if (l == visited.end() || r == visited.end() || l->second == nullptr ||
        r->second == nullptr)
      return n;

    const std::vector<CBV>& left = l->second->values;
    const std::vector<CBV>& right = r->second->values;

    // Both are sorted, so the intersection is a merge walk.
    CBV common = nullptr;
    size_t commonCount = 0;
    for (size_t i = 0, j = 0; i < left.size() && j < right.size();)
    {
      const int compare = CONSTANTBV::BitVector_Lexicompare(left[i], right[j]);
      if (compare < 0)
        i++;
      else if (compare > 0)
        j++;
      else
      {
        common = left[i];
        commonCount++;
        i++;
        j++;
      }
    }

    if (commonCount != 1)
      return n;

    const ASTNode commonNode = nf->CreateConstant(
        CONSTANTBV::BitVector_Clone(common), n[0].GetValueWidth());

    ASTNode newN =
        nf->CreateNode(AND, nf->CreateNode(EQ, commonNode, n[0]),
                       nf->CreateNode(EQ, commonNode, n[1]));
    replaceWithSimpler++;
    return newN;
  }

  //TODO merge these two toplevel funtions, they do the same thing..
  ASTNode StrengthReduction::topLevel(const ASTNode& top,   const NodeToFixedBitsMap& visited)
  {
    ASTNodeMap fromTo;

    for (auto it = visited.begin(); it != visited.end(); it++)
    {
      const ASTNode& n = it->first;
      if (n.isConstant())
        continue;

      ASTNode to = strengthReduction(n,visited);
      if (to != n)
        fromTo.insert({n,to});
    }

    ASTNode result = top;

    if (uf->stats_flag)
      stats();

    if (fromTo.size() > 0)
    {
      ASTNodeMap cache;
      result = SubstitutionMap::replace(result, fromTo, cache, nf);
    }

    return result;
  }

  // Replace some of the things that unsigned intervals can figure out for us.
  // Reduce from signed to unsigned if possible.
  ASTNode StrengthReduction::topLevel(const ASTNode& top,  const NodeToUnsignedIntervalMap& visited)
  {
    ASTNodeMap fromTo;
    for (auto it = visited.begin(); it != visited.end(); ++it)
    {
      const ASTNode& n = it->first;

      if (n.isConstant())
        continue;

      ASTNode newN = strengthReduction(n,visited);
      if (n != newN)
        fromTo.insert({n,newN});
    }

    ASTNode result = top;

    if (uf->stats_flag)
      stats();

    if (fromTo.size() > 0)
    {
      ASTNodeMap cache;
      result = SubstitutionMap::replace(result, fromTo, cache, nf);
    }

    return result;
  }

  ASTNode StrengthReduction::topLevel(const ASTNode& top,  const NodeToValueSetMap& visited)
  {
    ASTNodeMap fromTo;
    for (auto it = visited.begin(); it != visited.end(); ++it)
    {
      const ASTNode& n = it->first;

      if (n.isConstant())
        continue;

      ASTNode newN = strengthReduction(n,visited);
      if (n != newN)
        fromTo.insert({n,newN});
    }

    ASTNode result = top;

    if (uf->stats_flag)
      stats();

    if (fromTo.size() > 0)
    {
      ASTNodeMap cache;
      result = SubstitutionMap::replace(result, fromTo, cache, nf);
    }

    return result;
  }

  StrengthReduction::StrengthReduction(NodeFactory* _nf, UserDefinedFlags * _uf)
  {
    littleOne = CONSTANTBV::BitVector_Create(1, true);
    littleZero = CONSTANTBV::BitVector_Create(1, true);
    CONSTANTBV::BitVector_Fill(littleOne);
    nf = _nf;
    uf = _uf;

    replaceWithConstant = 0;
    replaceWithSimpler = 0;
  }

  StrengthReduction::~StrengthReduction()
  {
    CONSTANTBV::BitVector_Destroy(littleOne);
    CONSTANTBV::BitVector_Destroy(littleZero);
  }

  void StrengthReduction::stats(string name)
  {
    std::cerr << "{" << name
              << "} replace with constant: " << replaceWithConstant
              << std::endl;
    std::cerr << "{" << name
              << "} replace with simpler operation: " << replaceWithSimpler
              << std::endl;
  }
}

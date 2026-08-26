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
#include "stp/Util/CBVOps.h"
#include "stp/Util/DagWalk.h"
#include <iostream>

namespace stp
{
  using std::make_pair;
  using simplifier::constantBitP::FixedBits;

  // visit each node apply strength reductions to it.
  //
  // postOrderRebuild does the walking, on the heap: how deeply the input
  // nests is not this pass's choice, and a call per level exhausts the
  // stack. What is left here is the reduction of a single node.
  ASTNode StrengthReduction::visit(const ASTNode& n, NodeDomainAnalysis& nda, ASTNodeMap& cache)
  {
    return postOrderRebuild(
        n, cache, [&](const ASTNode& node, const ASTVec& children) {
          ASTNode newN;
          if (node.GetType() == BOOLEAN_TYPE)
            newN = nf->CreateNode(node.GetKind(), children);
          else
            newN = nf->CreateArrayTerm(node.GetKind(), node.GetIndexWidth(),
                                       node.GetValueWidth(), children);

          // buildMap memoises on the node, so it only needs redoing when the
          // preceding reduction actually replaced the node.
          nda.buildMap(newN);
          ASTNode reduced = strengthReduction(newN, *nda.getCbitMap());

          if (reduced != newN)
          {
            newN = reduced;
            nda.buildMap(newN);
          }
          reduced = strengthReduction(newN, *nda.getIntervalMap());

          if (reduced != newN)
          {
            newN = reduced;
            nda.buildMap(newN);
          }
          newN = strengthReduction(newN, *nda.getValueSetMap());

          return newN;
        });
  }

  ASTNode StrengthReduction::topLevel(const ASTNode& top, NodeDomainAnalysis& nda)
  {
    ASTNodeMap fromTo;
    ASTNode result = visit(top, nda, fromTo);
    if (uf->stats_flag)
      stats();
    return result;
  }

  // True unless the product of the operands' interval maxima provably
  // fits in `width` bits, i.e. the multiplication can't wrap. Both
  // maxima are zero-extended into 2w+1 bits so the signed
  // BitVector_Multiply computes the unsigned product.
  static bool multMayOverflow(const UnsignedInterval* a,
                              const UnsignedInterval* b, unsigned width)
  {
    if (a == nullptr || b == nullptr)
      return true;

    const unsigned ew = 2 * width + 1;
    CBV a2 = CONSTANTBV::BitVector_Create(ew, true);
    CBV b2 = CONSTANTBV::BitVector_Create(ew, true);
    CBV product = CONSTANTBV::BitVector_Create(ew, true);
    CONSTANTBV::BitVector_Interval_Copy(a2, a->maxV, 0, 0, width);
    CONSTANTBV::BitVector_Interval_Copy(b2, b->maxV, 0, 0, width);
    CONSTANTBV::BitVector_Multiply(product, a2, b2);

    bool overflow = false;
    for (unsigned i = width; i < ew && !overflow; i++)
      if (CONSTANTBV::BitVector_bit_test(product, i))
        overflow = true;

    CONSTANTBV::BitVector_Destroy(a2);
    CONSTANTBV::BitVector_Destroy(b2);
    CONSTANTBV::BitVector_Destroy(product);
    return overflow;
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
    else if (k == BVMOD)
    {
      // A remainder whose dividend is always below the divisor is the
      // dividend. (The quotient analogue needs no rule here: the
      // interval transfer for BVDIV computes a constant zero interval,
      // which is replaced above.)
      const auto l = visited.find(n[0]);
      const auto r = visited.find(n[1]);
      if (l != visited.end() && r != visited.end() && l->second != nullptr &&
          r->second != nullptr &&
          CONSTANTBV::BitVector_Lexicompare(l->second->maxV,
                                            r->second->minV) < 0)
      {
        newN = n[0];
        replaceWithSimpler++;
      }
    }
    else if (k == EQ)
    {
      // An equality whose sides' intervals meet at exactly one point
      // holds just when both sides take that value, so it splits into a
      // conjunction of equalities against a constant. This catches
      // sides with too many values for the set domain to track;
      // disjoint intervals don't need handling here, the equality's own
      // domain is then a constant false, which is replaced above.
      const auto l = visited.find(n[0]);
      const auto r = visited.find(n[1]);

      // With a constant on either side the equality already is a
      // comparison against a constant; the split would rebuild it.
      if (l != visited.end() && r != visited.end() && l->second != nullptr &&
          r->second != nullptr && !n[0].isConstant() && !n[1].isConstant())
      {
        const UnsignedInterval* a = l->second;
        const UnsignedInterval* b = r->second;

        const CBV lo =
            (CONSTANTBV::BitVector_Lexicompare(a->minV, b->minV) >= 0)
                ? a->minV
                : b->minV;
        const CBV hi =
            (CONSTANTBV::BitVector_Lexicompare(a->maxV, b->maxV) <= 0)
                ? a->maxV
                : b->maxV;

        if (CONSTANTBV::BitVector_Lexicompare(lo, hi) == 0)
        {
          const ASTNode touch = nf->CreateConstant(
              CONSTANTBV::BitVector_Clone(lo), n[0].GetValueWidth());
          // Named variables, so that the nodes aren't built in whatever order
          // the compiler picks to evaluate the arguments in.
          const ASTNode eq0 = nf->CreateNode(EQ, touch, n[0]);
          const ASTNode eq1 = nf->CreateNode(EQ, touch, n[1]);
          newN = nf->CreateNode(AND, eq0, eq1);
          replaceWithSimpler++;
        }
      }

      // (a * b) = (a * c) --> b = c, when a is provably non-zero and
      // neither multiplication can wrap: without wrapping the products
      // are integer products, and a non-zero common factor cancels.
      if (newN == n && n[0].GetKind() == BVMULT && n[0].Degree() == 2 &&
          n[1].GetKind() == BVMULT && n[1].Degree() == 2)
      {
        const auto get = [&visited](const ASTNode& m) -> const UnsignedInterval* {
          const auto it = visited.find(m);
          return it == visited.end() ? nullptr : it->second;
        };

        const unsigned width = n[0].GetValueWidth();

        for (unsigned i = 0; i < 2 && newN == n; i++)
          for (unsigned j = 0; j < 2 && newN == n; j++)
            if (n[0][i] == n[1][j])
            {
              const UnsignedInterval* shared = get(n[0][i]);
              if (shared != nullptr &&
                  !CONSTANTBV::BitVector_is_empty(shared->minV) &&
                  !multMayOverflow(get(n[0][0]), get(n[0][1]), width) &&
                  !multMayOverflow(get(n[1][0]), get(n[1][1]), width))
              {
                newN = nf->CreateNode(EQ, n[0][1 - i], n[1][1 - j]);
                replaceWithSimpler++;
              }
            }
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
      {
        // The replaced node's floating-point format (if it has one) must be
        // passed along: a constant is a leaf, so unlike the interior node it
        // stands in for it cannot derive a format from children. A bare
        // bitvector constant put where a float was makes the parent
        // operation's rebuild abort -- fp.neg of a constant folds by making
        // a floating-point constant, of format (0, 0) then.
        newN = nf->CreateConstant(b->GetBVConst(), n.GetValueWidth(),
                                  n.GetExpWidth(), n.GetSigWidth());
      }

      replaceWithConstant++;
    }
    else if (kind == BVSGT || kind == BVSGE || kind == SBVDIV ||
             kind == SBVMOD || kind == SBVREM || kind == BVSADDO ||
             kind == BVSSUBO)
    {
      const auto lIt = visited.find(n[0]);
      const auto rIt = visited.find(n[1]);
      if (lIt != visited.end() && rIt != visited.end())
        if (lIt->second != nullptr && rIt->second != nullptr)
        {
          const FixedBits* l = lIt->second;
          const FixedBits* r = rIt->second;
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
            else if (kind == BVSADDO &&
                     (l->getValue(bw - 1) != r->getValue(bw - 1)))
            {
              // Signed add overflow requires the operands to share a sign,
              // so opposite sign bits prove no overflow.
              newN = nf->getFalse();
              replaceWithSimpler++;
            }
            else if (kind == BVSSUBO &&
                     (l->getValue(bw - 1) == r->getValue(bw - 1)))
            {
              // Signed sub overflow requires the operands to differ in sign,
              // so equal sign bits prove no overflow.
              newN = nf->getFalse();
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
    else if (kind == EQ)
    {
      // (a * x) = (a * y) --> x = y, when a's lowest bit is fixed to
      // one: multiplication by an odd factor is a bijection mod 2^w,
      // so the factor cancels with no overflow condition.
      if (n[0].GetKind() == BVMULT && n[0].Degree() == 2 &&
          n[1].GetKind() == BVMULT && n[1].Degree() == 2)
      {
        for (unsigned i = 0; i < 2 && newN == n; i++)
          for (unsigned j = 0; j < 2 && newN == n; j++)
            if (n[0][i] == n[1][j])
            {
              const auto it = visited.find(n[0][i]);
              if (it != visited.end() && it->second != nullptr &&
                  it->second->isFixed(0) && it->second->getValue(0))
              {
                newN = nf->CreateNode(EQ, n[0][1 - i], n[1][1 - j]);
                replaceWithSimpler++;
              }
            }
      }
    }
    else if (kind == BVPLUS || kind == BVXOR)
    {
      // A pair of addends whose possibly-one bits are disjoint can never
      // carry into each other, so their sum is their bitwise-or. Peeling
      // such a pair out of an n-ary sum removes an adder stage. Unlike the
      // whole-node rule below this needs bit information for only the two
      // addends being paired, so it still applies when the rest are unknown.
      if (uf->enable_pair_extract && kind == BVPLUS && n.Degree() > 2)
      {
        const unsigned w = n.GetValueWidth();
        const unsigned words = (w + 63) / 64;

        // A group holds addends that are pairwise disjoint, so the group's
        // sum is its bitwise-or. Addends with no bit information sit in
        // singleton groups and never merge.
        vector<ASTVec> groups;
        vector<vector<uint64_t>> masks;
        vector<char> known;
        groups.reserve(n.Degree());
        masks.reserve(n.Degree());
        known.reserve(n.Degree());

        for (unsigned j = 0; j < n.Degree(); j++)
        {
          groups.push_back(ASTVec(1, n[j]));
          const auto it = visited.find(n[j]);
          const bool haveBits = (it != visited.end() && it->second != nullptr);
          known.push_back(haveBits ? 1 : 0);
          masks.push_back(vector<uint64_t>(words, 0));
          if (!haveBits)
            continue;
          for (unsigned i = 0; i < w; i++)
            if (!it->second->isFixed(i) || it->second->getValue(i))
              masks.back()[i / 64] |= (uint64_t(1) << (i % 64));
        }

        bool merged = false;
        for (unsigned x = 0; x < groups.size(); x++)
        {
          if (!known[x])
            continue;
          for (unsigned y = x + 1; y < groups.size();)
          {
            bool overlap = !known[y];
            for (unsigned k = 0; k < words && !overlap; k++)
              if (masks[x][k] & masks[y][k])
                overlap = true;
            if (overlap)
            {
              y++;
              continue;
            }
            for (unsigned k = 0; k < words; k++)
              masks[x][k] |= masks[y][k];
            groups[x].insert(groups[x].end(), groups[y].begin(),
                             groups[y].end());
            groups.erase(groups.begin() + y);
            masks.erase(masks.begin() + y);
            known.erase(known.begin() + y);
            merged = true;
          }
        }

        if (merged)
        {
          ASTVec newKids;
          newKids.reserve(groups.size());
          for (const auto& g : groups)
          {
            if (g.size() == 1)
            {
              newKids.push_back(g[0]);
              continue;
            }

            // The group's members are pairwise disjoint, so each bit is
            // owned by at most one of them and the group is just wiring:
            // a concatenation of slices of its members, with zero constants
            // where no member can be one.
            vector<int> owner(w, -1);
            for (unsigned m = 0; m < g.size(); m++)
            {
              const auto it = visited.find(g[m]);
              if (it == visited.end() || it->second == nullptr)
                continue;
              for (unsigned i = 0; i < w; i++)
                if (!it->second->isFixed(i) || it->second->getValue(i))
                  owner[i] = (int)m;
            }

            // Walk the maximal runs of equal ownership from the top down,
            // folding them into a right-leaning concatenation.
            ASTNode acc;
            unsigned accWidth = 0;
            unsigned hi = w;
            while (hi > 0)
            {
              unsigned lo = hi - 1;
              while (lo > 0 && owner[lo - 1] == owner[hi - 1])
                lo--;
              const unsigned pieceWidth = hi - lo;
              const ASTNode piece =
                  (owner[hi - 1] < 0)
                      ? nf->CreateZeroConst(pieceWidth)
                      : nf->CreateTerm(BVEXTRACT, pieceWidth, g[owner[hi - 1]],
                                       nf->CreateBVConst(32, hi - 1),
                                       nf->CreateBVConst(32, lo));
              if (accWidth == 0)
                acc = piece;
              else
                acc = nf->CreateTerm(BVCONCAT, accWidth + pieceWidth, acc,
                                     piece);
              accWidth += pieceWidth;
              hi = lo;
            }
            newKids.push_back(acc);
          }

          newN = (newKids.size() == 1) ? newKids[0]
                                       : nf->CreateTerm(BVPLUS, w, newKids);
          replaceWithSimpler++;
          return newN;
        }
      }

      // If all the bits are zero except for one, in each position, replace by OR
      vector<FixedBits*> children;
      bool bad = false;
      for (ASTNode c : n.GetChildren())
      {
        const auto it = visited.find(c);
        if (it == visited.end() || it->second == nullptr)
        {
          bad = true;
          break;
        }
        children.push_back(it->second);
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
              nf->CreateTerm(BVOR, n.GetValueWidth(), toASTVec(n.GetChildren()));
          replaceWithSimpler++;

          // When the disjointness is a contiguous split, the OR is just
          // wiring: the high part concatenated onto the low part.
          if (n.Degree() == 2)
          {
            const unsigned width = n.GetValueWidth();
            for (unsigned i = 0; i < 2; i++)
            {
              const FixedBits* high = children[i];
              const FixedBits* low = children[1 - i];

              // The lowest bit of "high" that might be one.
              unsigned k = 0;
              while (k < width && high->isFixed(k) && !high->getValue(k))
                k++;

              // All of "low"'s possibly-one bits must sit below k.
              bool lowFits = true;
              for (unsigned j = k; j < width && lowFits; j++)
                if (!(low->isFixed(j) && !low->getValue(j)))
                  lowFits = false;

              if (lowFits && k > 0 && k < width)
              {
                const ASTNode top = nf->CreateTerm(
                    BVEXTRACT, width - k, n[i],
                    nf->CreateBVConst(32, width - 1),
                    nf->CreateBVConst(32, k));
                const ASTNode bottom = nf->CreateTerm(
                    BVEXTRACT, k, n[1 - i], nf->CreateBVConst(32, k - 1),
                    nf->CreateBVConst(32, 0));
                newN = nf->CreateTerm(BVCONCAT, width, top, bottom);
                break;
              }
            }
          }
        }
        else if (kind == BVPLUS)
        {
          // Leading zeros on every operand bound the sum, so the
          // addition narrows to the width that can carry.
          const unsigned width = n.GetValueWidth();

          unsigned maxEffective = 0;
          for (unsigned i = 0; i < children.size(); i++)
          {
            unsigned nlz = 0;
            while (nlz < width && children[i]->isFixed(width - 1 - nlz) &&
                   !children[i]->getValue(width - 1 - nlz))
              nlz++;
            if (width - nlz > maxEffective)
              maxEffective = width - nlz;
          }

          // Adding m terms can carry ceil(log2(m)) bits upwards.
          unsigned carry = 0;
          while ((1u << carry) < children.size())
            carry++;

          const unsigned rest = maxEffective + carry;
          if (maxEffective > 0 && rest < width)
          {
            ASTVec narrowed;
            narrowed.reserve(n.Degree());
            for (const auto& c : n.GetChildren())
              narrowed.push_back(
                  nf->CreateTerm(BVEXTRACT, rest, c,
                                 nf->CreateBVConst(32, rest - 1),
                                 nf->CreateBVConst(32, 0)));

            newN = nf->CreateTerm(
                BVCONCAT, width, nf->CreateZeroConst(width - rest),
                nf->CreateTerm(BVPLUS, rest, narrowed));
            replaceWithSimpler++;
          }
        }
      }
    }
    else if (kind == BVMULT)
    {
      // Leading zeros on the operands bound the product, so the
      // multiplication narrows to the width the product can occupy.
      const unsigned width = n.GetValueWidth();

      bool bad = false;
      unsigned totalEffective = 0;
      for (const auto& c : n.GetChildren())
      {
        const auto it = visited.find(c);
        if (it == visited.end() || it->second == nullptr)
        {
          bad = true;
          break;
        }

        unsigned nlz = 0;
        while (nlz < width - 1 && it->second->isFixed(width - 1 - nlz) &&
               !it->second->getValue(width - 1 - nlz))
          nlz++;
        totalEffective += width - nlz;
      }

      if (!bad && totalEffective < width)
      {
        const unsigned rest = totalEffective;

        ASTVec narrowed;
        narrowed.reserve(n.Degree());
        for (const auto& c : n.GetChildren())
          narrowed.push_back(nf->CreateTerm(BVEXTRACT, rest, c,
                                            nf->CreateBVConst(32, rest - 1),
                                            nf->CreateBVConst(32, 0)));

        newN = nf->CreateTerm(
            BVCONCAT, width, nf->CreateZeroConst(width - rest),
            nf->CreateTerm(BVMULT, rest, narrowed));
        replaceWithSimpler++;
      }
    }
    else if (kind == BVDIV || kind == BVMOD)
    {
      // If the dividend's leading bits are zero, the interesting part
      // fits into the remaining width, so narrow the operation, guarded
      // on the divisor's leading bits being zero too. When they aren't,
      // the divisor exceeds the dividend, making the quotient zero and
      // the remainder the dividend. Division additionally needs the
      // divisor to be provably non-zero, because the narrowed form
      // wouldn't recreate the all-ones result at full width.
      const auto l = visited.find(n[0]);
      const auto r = visited.find(n[1]);
      if (l != visited.end() && r != visited.end() && l->second != nullptr &&
          r->second != nullptr)
      {
        const FixedBits* dividend = l->second;
        const FixedBits* divisor = r->second;
        const unsigned width = n.GetValueWidth();

        unsigned nlz = 0;
        while (nlz < width - 1 && dividend->isFixed(width - 1 - nlz) &&
               !dividend->getValue(width - 1 - nlz))
          nlz++;

        bool divisorNonZero = false;
        for (unsigned i = 0; i < width; i++)
          if (divisor->isFixed(i) && divisor->getValue(i))
          {
            divisorNonZero = true;
            break;
          }

        if (nlz > 0 && (kind == BVMOD || divisorNonZero))
        {
          const unsigned rest = width - nlz;

          const ASTNode cond = nf->CreateNode(
              EQ, nf->CreateZeroConst(nlz),
              nf->CreateTerm(BVEXTRACT, nlz, n[1],
                             nf->CreateBVConst(32, width - 1),
                             nf->CreateBVConst(32, rest)));

          const ASTNode lhs =
              nf->CreateTerm(BVEXTRACT, rest, n[0],
                             nf->CreateBVConst(32, rest - 1),
                             nf->CreateBVConst(32, 0));
          const ASTNode rhs =
              nf->CreateTerm(BVEXTRACT, rest, n[1],
                             nf->CreateBVConst(32, rest - 1),
                             nf->CreateBVConst(32, 0));
          const ASTNode narrowed =
              nf->CreateTerm(BVCONCAT, width, nf->CreateZeroConst(nlz),
                             nf->CreateTerm(kind, rest, lhs, rhs));

          const ASTNode otherwise =
              (kind == BVDIV) ? nf->CreateZeroConst(width) : n[0];

          newN = nf->CreateTerm(ITE, width, cond, narrowed, otherwise);
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

    const ASTNode eq0 = nf->CreateNode(EQ, commonNode, n[0]);
    const ASTNode eq1 = nf->CreateNode(EQ, commonNode, n[1]);
    ASTNode newN = nf->CreateNode(AND, eq0, eq1);
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
    littleOne = mkOne(1);
    nf = _nf;
    uf = _uf;

    replaceWithConstant = 0;
    replaceWithSimpler = 0;
  }

  StrengthReduction::~StrengthReduction()
  {
    CONSTANTBV::BitVector_Destroy(littleOne);
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

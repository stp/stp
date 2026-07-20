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

#include "stp/Simplifier/UnsignedIntervalSetAnalysis.h"

namespace stp
{

// Whether child 'i' should be split at the sign boundary: only the operands
// that are interpreted as signed. For an arithmetic shift and the unary
// negations/extends just the first operand is signed; the shift amount is
// unsigned, so splitting it only multiplies the work.
bool UnsignedIntervalSetAnalysis::splitChild(Kind k, unsigned i)
{
  switch (k)
  {
    case BVSGT:
    case BVSGE:
    case SBVDIV:
    case SBVREM:
    case SBVMOD:
      return true; // both operands are signed
    case BVSRSHIFT:
    case BVSX:
    case BVUMINUS:
      return i == 0; // only the value operand is signed
    default:
      return false;
  }
}

namespace
{
// Splits p into at most two sign-consistent pieces: the part below the sign
// bit and the part at/above it. This is all the signed transfer functions
// need (they resolve zero and type-min internally), so it is cheaper than
// UnsignedInterval::split, which also isolates 0 and the signed minimum.
void splitAtSignBoundary(const UnsignedInterval* p, unsigned w,
                         std::vector<UnsignedInterval*>& out)
{
  const bool minNeg = CONSTANTBV::BitVector_bit_test(p->minV, w - 1);
  const bool maxNeg = CONSTANTBV::BitVector_bit_test(p->maxV, w - 1);

  if (minNeg == maxNeg) // wholly within one hemisphere
  {
    out.push_back(new UnsignedInterval(CONSTANTBV::BitVector_Clone(p->minV),
                                       CONSTANTBV::BitVector_Clone(p->maxV)));
    return;
  }

  // [minV, 0111..1] and [1000..0, maxV].
  CBV lowHi = CONSTANTBV::BitVector_Create(w, true);
  CONSTANTBV::BitVector_Fill(lowHi);
  CONSTANTBV::BitVector_Bit_Off(lowHi, w - 1); // signBit - 1
  CBV highLo = CONSTANTBV::BitVector_Create(w, true);
  CONSTANTBV::BitVector_Bit_On(highLo, w - 1); // signBit

  out.push_back(
      new UnsignedInterval(CONSTANTBV::BitVector_Clone(p->minV), lowHi));
  out.push_back(
      new UnsignedInterval(highLo, CONSTANTBV::BitVector_Clone(p->maxV)));
}

// References to the pieces of one child. A missing or complete child
// contributes a single complete interval; the signed kinds split each part
// at the sign poles. Pieces that had to be allocated (complete fillers and
// split results) are recorded in 'owned' for later deletion; unsplit parts
// are aliased straight from the set with no allocation.
void collectPieceRefs(const ASTNode& childNode, const UnsignedIntervalSet* set,
                      bool split, std::vector<const UnsignedInterval*>& refs,
                      std::vector<UnsignedInterval*>& owned)
{
  const unsigned w = std::max((unsigned)1, childNode.GetValueWidth());

  if (set == nullptr || set->isComplete())
  {
    // Match dispatchToTransferFunctions' contract: an unknown/complete child
    // is passed as NULL (not a complete interval), so transfer functions that
    // are only defined for a known child -- e.g. NOT asserting its operand is
    // constant -- see "no information" instead of a non-constant full range.
    refs.push_back(nullptr);
    return;
  }

  for (const UnsignedInterval* p : set->parts)
  {
    if (split && w > 1)
    {
      std::vector<UnsignedInterval*> tmp;
      splitAtSignBoundary(p, w, tmp);
      for (UnsignedInterval* t : tmp)
      {
        owned.push_back(t);
        refs.push_back(t);
      }
    }
    else
      refs.push_back(p); // alias: no allocation, not owned
  }
}
} // namespace

UnsignedIntervalSet* UnsignedIntervalSetAnalysis::transfer(
    const ASTNode& n, const std::vector<const UnsignedIntervalSet*>& children)
{
  const unsigned width = std::max((unsigned)1, n.GetValueWidth());
  const unsigned number = n.Degree();
  const Kind kind = n.GetKind();

  UnsignedIntervalSet* out = new UnsignedIntervalSet(width, cap);

  // ITE: the value set is the union of the taken branches. No cross-product.
  if (kind == ITE)
  {
    const UnsignedIntervalSet* cond = children[0];
    const UnsignedIntervalSet* thenS = children[1];
    const UnsignedIntervalSet* elseS = children[2];

    bool takeThen = true, takeElse = true;
    if (cond != nullptr && cond->isConstant())
    {
      const bool one = CONSTANTBV::BitVector_bit_test(cond->parts[0]->minV, 0);
      takeThen = one;
      takeElse = !one;
    }

    if (takeThen)
    {
      if (thenS == nullptr || thenS->isComplete())
      {
        out->resetToComplete();
        return out;
      }
      out->addSet(*thenS);
    }
    if (takeElse)
    {
      if (elseS == nullptr || elseS->isComplete())
      {
        out->resetToComplete();
        return out;
      }
      out->addSet(*elseS);
    }
    return out;
  }

  // General: cross-product of the children's pieces through the existing
  // single-interval transfer functions. Results are accumulated raw and the
  // set is normalised once at the end.
  std::vector<UnsignedInterval*> owned;
  std::vector<std::vector<const UnsignedInterval*>> pieces(number);
  for (unsigned i = 0; i < number; i++)
  {
    const UnsignedIntervalSet* s = (i < children.size()) ? children[i] : nullptr;
    collectPieceRefs(n[i], s, splitChild(kind, i), pieces[i], owned);
    if (pieces[i].empty()) // an empty child set: nothing is reachable
    {
      for (auto* p : owned)
        delete p;
      return out; // leave 'out' empty (bottom)
    }
  }

  std::vector<const UnsignedInterval*> combo(number);
  std::vector<unsigned> idx(number, 0);
  bool complete = false;

  // A width-1 (predicate) result saturates to complete once both 0 and 1
  // appear; stop early then instead of running the rest of the product.
  const bool smallResult = (width == 1);
  unsigned seenMask = 0;

  while (true)
  {
    for (unsigned i = 0; i < number; i++)
      combo[i] = pieces[i][idx[i]];

    UnsignedInterval* r = ia.dispatchToTransferFunctions(n, combo);
    if (r == nullptr) // a piece carried no information: union is complete
    {
      complete = true;
      break;
    }
    if (smallResult)
    {
      seenMask |= CONSTANTBV::BitVector_bit_test(r->minV, 0) ? 2u : 1u;
      if (seenMask == 3u)
      {
        delete r;
        complete = true;
        break;
      }
    }
    out->appendOwned(r); // take ownership, no clone

    // Odometer step over the piece indices.
    unsigned carry = 0;
    for (; carry < number; carry++)
    {
      if (++idx[carry] < pieces[carry].size())
        break;
      idx[carry] = 0;
    }
    if (carry == number)
      break;
  }

  for (auto* p : owned)
    delete p;

  if (complete)
    out->resetToComplete();
  else
    out->finalize();
  return out;
}
}

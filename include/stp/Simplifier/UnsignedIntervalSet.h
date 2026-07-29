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

/*
 * A bounded set of disjoint unsigned intervals.
 *
 * Like UnsignedInterval, but keeps a sorted list of disjoint,
 * non-adjacent intervals instead of a single [min,max]. When the list
 * grows past 'cap', the two neighbouring intervals separated by the
 * smallest gap are joined -- absorbing the gap between them -- until the
 * list is back under the cap. Joining only ever widens the set, so the
 * result is always a sound over-approximation, and the single-interval
 * domain is exactly the cap==1 case.
 */

#ifndef UNSIGNEDINTERVALSET_H_
#define UNSIGNEDINTERVALSET_H_

#include "stp/Simplifier/UnsignedInterval.h"
#include <algorithm>
#include <vector>

namespace stp
{

class UnsignedIntervalSet
{
public:
  // The default cap. Small is enough for the common sign-split and ITE
  // shapes (negative piece, zero, positive piece); the benchmark can
  // sweep it.
  static const unsigned DEFAULT_CAP = 4;

  unsigned width;
  unsigned cap;
  // Sorted ascending by minV; disjoint and non-adjacent (a gap of >= 1
  // integer separates consecutive parts). Each part owns its CBVs.
  std::vector<UnsignedInterval*> parts;

  explicit UnsignedIntervalSet(unsigned width_, unsigned cap_ = DEFAULT_CAP)
      : width(width_), cap(cap_ == 0 ? 1 : cap_)
  {
  }

  ~UnsignedIntervalSet() { clear(); }

  UnsignedIntervalSet(const UnsignedIntervalSet&) = delete;
  UnsignedIntervalSet& operator=(const UnsignedIntervalSet&) = delete;

  bool empty() const { return parts.empty(); }
  size_t size() const { return parts.size(); }

  // Unions the closed interval [lo, hi] into the set, restoring the
  // sorted/disjoint invariant and collapsing back to the cap. The
  // caller keeps ownership of lo/hi (they are cloned).
  void addInterval(const CBV lo, const CBV hi)
  {
    assert(bits_(lo) == width && bits_(hi) == width);
    assert(CONSTANTBV::BitVector_Lexicompare(lo, hi) <= 0);
    parts.push_back(new UnsignedInterval(CONSTANTBV::BitVector_Clone(lo),
                                         CONSTANTBV::BitVector_Clone(hi)));
    normalize();
    collapse();
  }

  // Appends a part directly, taking ownership, WITHOUT restoring the
  // sorted/disjoint invariant or the cap. Used for bulk accumulation; the
  // caller must call finalize() before the set is read.
  void appendOwned(UnsignedInterval* iv)
  {
    assert(iv->getWidth() == width);
    parts.push_back(iv);
  }

  // Restores the invariant after a run of appendOwned() calls.
  void finalize()
  {
    normalize();
    collapse();
  }

  // Unions another set (same width) into this one.
  void addSet(const UnsignedIntervalSet& other)
  {
    assert(other.width == width);
    for (const auto* p : other.parts)
      parts.push_back(new UnsignedInterval(
          CONSTANTBV::BitVector_Clone(p->minV),
          CONSTANTBV::BitVector_Clone(p->maxV)));
    normalize();
    collapse();
  }

  // Discards everything and becomes the full range [0, 2^width-1] (top).
  void resetToComplete()
  {
    clear();
    CBV lo = CONSTANTBV::BitVector_Create(width, true);
    CBV hi = CONSTANTBV::BitVector_Create(width, true);
    CONSTANTBV::BitVector_Fill(hi);
    parts.push_back(new UnsignedInterval(lo, hi));
  }

  // Intersects the set with the closed interval [lo, hi], trimming or
  // dropping parts that fall outside. Keeps the sorted/disjoint invariant.
  void intersectInterval(const CBV lo, const CBV hi)
  {
    assert(bits_(lo) == width && bits_(hi) == width);
    std::vector<UnsignedInterval*> keep;
    for (auto* p : parts)
    {
      // new lo = max(p->minV, lo); new hi = min(p->maxV, hi)
      const bool loInside =
          CONSTANTBV::BitVector_Lexicompare(p->minV, lo) >= 0;
      const bool hiInside =
          CONSTANTBV::BitVector_Lexicompare(p->maxV, hi) <= 0;
      CBV nlo = loInside ? p->minV : lo;
      CBV nhi = hiInside ? p->maxV : hi;
      if (CONSTANTBV::BitVector_Lexicompare(nlo, nhi) > 0)
      {
        delete p; // wholly outside
        continue;
      }
      if (!loInside)
        CONSTANTBV::BitVector_Copy(p->minV, lo);
      if (!hiInside)
        CONSTANTBV::BitVector_Copy(p->maxV, hi);
      keep.push_back(p);
    }
    parts.swap(keep);
  }

  bool isComplete() const
  {
    return parts.size() == 1 && parts[0]->isComplete();
  }

  bool isConstant() const
  {
    return parts.size() == 1 && parts[0]->isConstant();
  }

  bool in(const CBV c) const
  {
    for (const auto* p : parts)
      if (p->in(c))
        return true;
    return false;
  }

  // The smallest single interval containing the whole set, or nullptr if
  // that interval is the complete range (matching the analysis'
  // "null means top" convention). Caller owns the returned interval.
  UnsignedInterval* hull() const
  {
    if (parts.empty())
      return nullptr;
    if (isComplete())
      return nullptr;
    return new UnsignedInterval(
        CONSTANTBV::BitVector_Clone(parts.front()->minV),
        CONSTANTBV::BitVector_Clone(parts.back()->maxV));
  }

  void checkInvariant() const
  {
#ifndef NDEBUG
    assert(parts.size() <= cap);
    for (size_t i = 0; i < parts.size(); i++)
    {
      assert(parts[i]->getWidth() == width);
      parts[i]->checkUnsignedInvariant();
      if (i > 0)
      {
        // strictly increasing and non-adjacent: parts[i].min must be at
        // least parts[i-1].max + 2 (a real gap of >= 1 between them).
        assert(!touches(parts[i - 1], parts[i]));
      }
    }
#endif
  }

private:
  void clear()
  {
    for (auto* p : parts)
      delete p;
    parts.clear();
  }

  // True when b starts at or before a.max + 1, i.e. [a] and [b] overlap
  // or abut and must be merged. Assumes a.min <= b.min. Saturates at the
  // top so a.max == all-ones never overflows.
  static bool touches(const UnsignedInterval* a, const UnsignedInterval* b)
  {
    if (CONSTANTBV::BitVector_is_full(a->maxV))
      return true;
    CBV t = CONSTANTBV::BitVector_Clone(a->maxV);
    CONSTANTBV::BitVector_increment(t);
    const int c = CONSTANTBV::BitVector_Lexicompare(b->minV, t);
    CONSTANTBV::BitVector_Destroy(t);
    return c <= 0;
  }

  // Sorts and merges overlapping/adjacent parts so the list is sorted,
  // disjoint and non-adjacent.
  void normalize()
  {
    std::sort(parts.begin(), parts.end(),
              [](const UnsignedInterval* x, const UnsignedInterval* y) {
                return CONSTANTBV::BitVector_Lexicompare(x->minV, y->minV) < 0;
              });

    std::vector<UnsignedInterval*> out;
    for (auto* p : parts)
    {
      if (!out.empty() && touches(out.back(), p))
      {
        UnsignedInterval* back = out.back();
        if (CONSTANTBV::BitVector_Lexicompare(p->maxV, back->maxV) > 0)
          CONSTANTBV::BitVector_Copy(back->maxV, p->maxV);
        delete p;
      }
      else
        out.push_back(p);
    }
    parts.swap(out);
  }

  // Repeatedly joins the adjacent pair separated by the smallest gap
  // until the list fits the cap. Joining fills the gap, so the closest
  // intervals merge first.
  void collapse()
  {
    if (parts.size() <= cap)
      return;

    CBV gap = CONSTANTBV::BitVector_Create(width, true);
    CBV best = CONSTANTBV::BitVector_Create(width, true);

    while (parts.size() > cap)
    {
      size_t bestI = 0;
      bool haveBest = false;
      for (size_t i = 0; i + 1 < parts.size(); i++)
      {
        CONSTANTBV::boolean carry = 0;
        // gap = parts[i+1].min - parts[i].max  (>= 2, no borrow)
        CONSTANTBV::BitVector_sub(gap, parts[i + 1]->minV, parts[i]->maxV,
                                  &carry);
        if (!haveBest ||
            CONSTANTBV::BitVector_Lexicompare(gap, best) < 0)
        {
          CONSTANTBV::BitVector_Copy(best, gap);
          bestI = i;
          haveBest = true;
        }
      }

      // Merge bestI and bestI+1 into one [min_i, max_{i+1}].
      CONSTANTBV::BitVector_Copy(parts[bestI]->maxV, parts[bestI + 1]->maxV);
      delete parts[bestI + 1];
      parts.erase(parts.begin() + bestI + 1);
    }

    CONSTANTBV::BitVector_Destroy(gap);
    CONSTANTBV::BitVector_Destroy(best);
  }
};
}
#endif

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
 * Holds a small set of the values a node can take. Sets that would
 * exceed MAX_ELEMENTS are widened away to "unknown" (a null pointer)
 * by the code that builds them.
 */

#ifndef VALUESET_H_
#define VALUESET_H_

#include "stp/AST/AST.h"
#include <algorithm>
#include <iostream>
#include <vector>

namespace stp
{

struct ValueSet
{
  static const size_t MAX_ELEMENTS = 12;

  // Sorted ascending by unsigned comparison, no duplicates. Owned.
  std::vector<CBV> values;

  unsigned width; // 1 for booleans.
  bool representsBoolean;

  ValueSet(unsigned _width, bool isBoolean)
      : width(_width), representsBoolean(isBoolean)
  {
    assert(!isBoolean || _width == 1);
  }

  ~ValueSet()
  {
    for (CBV v : values)
      CONSTANTBV::BitVector_Destroy(v);
  }

  ValueSet(ValueSet const&) = delete;
  ValueSet& operator=(ValueSet const&) = delete;

  // Takes ownership of v, which is destroyed if it's already a member.
  // Returns false without changing the set if adding would exceed
  // MAX_ELEMENTS; the caller then discards the whole set, widening to
  // "unknown".
  bool insert(CBV v)
  {
    assert(bits_(v) == width);

    const auto it = lowerBound(v);
    if (it != values.end() && !CONSTANTBV::BitVector_Lexicompare(*it, v))
    {
      CONSTANTBV::BitVector_Destroy(v);
      return true;
    }
    if (values.size() >= MAX_ELEMENTS)
    {
      CONSTANTBV::BitVector_Destroy(v);
      return false;
    }
    values.insert(it, v);
    return true;
  }

  bool in(const CBV c) const
  {
    assert(bits_(c) == width);
    const auto it = lowerBound(c);
    return it != values.end() && !CONSTANTBV::BitVector_Lexicompare(*it, c);
  }

  size_t size() const { return values.size(); }

  bool isConstant() const { return values.size() == 1; }

  // Whether the set holds every value of the width, i.e. no information.
  bool isComplete() const
  {
    return width < 4 && values.size() == ((size_t)1 << width);
  }

  unsigned getWidth() const { return width; }

  bool isBoolean() const { return representsBoolean; }

  // The extreme members. Still owned by the set.
  CBV smallest() const
  {
    assert(!values.empty());
    return values.front();
  }

  CBV largest() const
  {
    assert(!values.empty());
    return values.back();
  }

  void print() const
  {
    for (CBV v : values)
    {
      unsigned char* s = CONSTANTBV::BitVector_to_Bin(v);
      std::cerr << s << " ";
      free(s);
    }
    std::cerr << std::endl;
  }

private:
  std::vector<CBV>::const_iterator lowerBound(const CBV v) const
  {
    return std::lower_bound(values.begin(), values.end(), v,
                            [](const CBV a, const CBV b) {
                              return CONSTANTBV::BitVector_Lexicompare(a, b) <
                                     0;
                            });
  }
};
}
#endif

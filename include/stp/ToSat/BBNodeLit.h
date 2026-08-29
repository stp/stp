/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: August, 2026
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

#ifndef BBNODELIT_H
#define BBNODELIT_H

#include "stp/AIG/Literal.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <ostream>

namespace stp
{

// The blaster's handle on a node of the in-house AIG: one literal, four
// bytes, no pointer.
//
// BBNodeAIG is sixteen -- an Aig_Obj_t* and an int symbol_index -- and the
// ordinal is what most of that pays for. It exists because dag-aware
// rewriting replaces ABC's manager wholesale and renumbers everything, so a
// symbol has to be found again by its position among the inputs. Nothing
// renumbers here: the id is the array index and the array only ever grows,
// so the literal *is* the identity and no ordinal has to be carried beside
// it.
//
// Null is aig::LIT_NULL, which is outside the literal space and closed under
// negation there -- so a null handle cannot be mistaken for a real node, and
// neither can its complement.
class BBNodeLit
{
public:
  aig::Lit n = aig::LIT_NULL;

  BBNodeLit() = default;
  explicit BBNodeLit(aig::Lit l) : n(l) {}

  bool IsNull() const { return n == aig::LIT_NULL; }

  // The whole literal, complement bit included, which is what the blaster's
  // memo tables need to distinguish x from !x. BBNodeAIG's own hash had to be
  // fixed to do the same.
  unsigned GetNodeNum() const { return n; }

  bool operator==(const BBNodeLit& o) const { return n == o.n; }
  bool operator!=(const BBNodeLit& o) const { return n != o.n; }

  // Not dead, whatever a grep suggests: mult_Booth sorts each column of
  // partial products with it, and that ordering decides which products
  // combine first, so it reaches the emitted formula. BBNodeAIG carries the
  // same operator for the same reason.
  bool operator<(const BBNodeLit& o) const { return n < o.n; }
};

static_assert(sizeof(BBNodeLit) == 4, "the point of this class is its size");

// For the --debug-multiply tracing. The AIG side answers this with a
// FatalError because an Aig_Obj_t* has nothing short to say; a literal does.
inline std::ostream& operator<<(std::ostream& out, const BBNodeLit& n)
{
  if (n.IsNull())
    return out << "null";
  if (aig::isNeg(n.n))
    out << '!';
  return out << aig::nodeOf(n.n);
}

} // namespace stp

namespace std
{
template <> struct hash<stp::BBNodeLit>
{
  size_t operator()(const stp::BBNodeLit& n) const
  {
    return std::hash<stp::aig::Lit>()(n.n);
  }
};
} // namespace std

#endif

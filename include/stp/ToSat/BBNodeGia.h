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

#ifndef BBNODEGIA_H
#define BBNODEGIA_H

#include <cstddef>
#include <functional>
#include <ostream>

namespace stp
{

// The blaster's handle on a node of an ABC Gia: one literal, four bytes.
//
// A Gia literal is 2*id + complement, and the id indexes Gia_Man_t::pObjs --
// an array that reallocs as it grows, so a Gia_Obj_t* would dangle the moment
// the next gate is built. That is why this backend cannot reuse BBNodeAIG's
// pointer handle. It is also why the literal needs no ordinal beside it the
// way BBNodeAIG does: nothing renumbers a Gia in place, and a CI carries its
// own ordinal in the object, so ciOrdinal() is a field read rather than
// something the handle has to remember.
//
// Null is negative. Gia literals are non-negative, so no real node can be
// mistaken for null -- and neither can the negation of one, since `^1` of a
// negative int stays negative. A null that survived a negation would
// otherwise alias literal 0 or 1, which are the two constants.
class BBNodeGia
{
public:
  int n = -1;

  BBNodeGia() = default;
  explicit BBNodeGia(int lit) : n(lit) {}

  bool IsNull() const { return n < 0; }

  // The whole literal, complement bit included, which is what the blaster's
  // memo tables need to distinguish x from !x.
  int GetNodeNum() const { return n; }

  bool operator==(const BBNodeGia& o) const { return n == o.n; }
  bool operator!=(const BBNodeGia& o) const { return n != o.n; }

  // Not dead, whatever a grep suggests: mult_Booth sorts each column of
  // partial products with it, and that ordering decides which products
  // combine first, so it reaches the emitted formula. Both other handles
  // carry the same operator for the same reason.
  bool operator<(const BBNodeGia& o) const { return n < o.n; }
};

static_assert(sizeof(BBNodeGia) == 4, "the point of this class is its size");

// For the --debug-multiply tracing, as BBNodeLit does. The ABC-Aig side
// answers this with a FatalError because an Aig_Obj_t* has nothing short to
// say; a literal does.
inline std::ostream& operator<<(std::ostream& out, const BBNodeGia& n)
{
  if (n.IsNull())
    return out << "null";
  if (n.n & 1)
    out << '!';
  return out << (n.n >> 1);
}

} // namespace stp

namespace std
{
template <> struct hash<stp::BBNodeGia>
{
  size_t operator()(const stp::BBNodeGia& n) const
  {
    return std::hash<int>()(n.n);
  }
};
} // namespace std

#endif

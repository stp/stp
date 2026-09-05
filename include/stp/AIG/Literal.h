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

#ifndef STP_AIG_LITERAL_H
#define STP_AIG_LITERAL_H

#include <cstdint>

namespace stp
{
namespace aig
{

// A node is an index into the manager's array; a literal is that index with
// the inverting bit in the low position, which is AIGER's convention:
// literal 0 is constant false, 1 is constant true, and negation is `^ 1`.
//
// Nothing here is a pointer. Node identity is a creation counter, so nothing
// downstream can come to depend on an address, an allocator, or the order two
// objects happened to land in memory -- which is the whole reason the AIG STP
// builds today has to be built through ordered wrappers.
using Node = uint32_t;
using Lit = uint32_t;

constexpr Lit LIT_FALSE = 0;
constexpr Lit LIT_TRUE = 1;

// Both slots of a CI or of the constant node hold this. It is deliberately
// outside the literal space *and closed under negation there*: the two-level
// rules below compare grandchildren without first asking whether the operand
// has any, so a sentinel that could equal a real literal -- or whose negation
// could -- would make a rule fire on a node that has no children.
constexpr Lit LIT_NULL = UINT32_MAX;

// The node count is capped so that `2*node + 1` stays inside a Lit, which
// also keeps LIT_NULL and LIT_NULL^1 unreachable.
constexpr uint32_t MAX_NODES = (UINT32_MAX / 2) - 1;

inline Lit neg(Lit l) { return l ^ 1u; }
inline Lit negIf(Lit l, bool c) { return l ^ static_cast<Lit>(c); }
inline bool isNeg(Lit l) { return (l & 1u) != 0; }
inline Node nodeOf(Lit l) { return l >> 1; }
inline Lit litOf(Node n, bool complement = false)
{
  return (static_cast<Lit>(n) << 1) | static_cast<Lit>(complement);
}
// Both constants live in node 0, so one comparison covers them.
inline bool isConst(Lit l) { return l <= LIT_TRUE; }

} // namespace aig
} // namespace stp

#endif

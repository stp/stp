/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

#ifndef STP_ARRAYOPS_H
#define STP_ARRAYOPS_H

#include "stp/AST/ASTNode.h"
#include "stp/AST/SourceSort.h"
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

class NodeFactory;

namespace stp
{
class STPMgr;

// Arrays use nonzero-width bit-vector carriers. Boolean source operands are
// represented by one bit, without identifying Bool with (_ BitVec 1).
ASTNode packBoolean(NodeFactory& nf, const ASTNode& value);
ASTNode unpackBoolean(NodeFactory& nf, const ASTNode& bits);
ASTNode createArrayRead(NodeFactory& nf, const ASTNode& array,
                        const ASTNode& index);
ASTNode createArrayWrite(NodeFactory& nf, const ASTNode& array,
                         const ASTNode& index, const ASTNode& value);

// Recognise a source select (or its negation when negated is true), including
// the simplifying factory's !(read == 0) spelling. A plain READ remains a
// bit-vector expression inside the engine.
ASTNode booleanArrayRead(const ASTNode& value, bool negated = false);

// ---- canonical constant arrays ----
//
// A store chain over a constant array whose indexes are all constants has
// one canonical form: no two stores at one index, no store of the default,
// the indexes ascending from the innermost store outwards, and -- when the
// index sort is small enough for the stores to cover half of it -- the
// default the most frequent cell value, a tie going to the value with the
// smaller bits. The simplifying factory keeps chains in it as it builds
// them.
//
// Only bit-vector and Boolean index sorts qualify: their constants are equal
// exactly when their bits are. Two float indexes with different NaN bits are
// one index, so reordering stores at them would change the array.
bool canonicalIndexSort(const SourceSort& index);

// A plain bit-vector constant: not a float, rounding-mode or declared-sort
// constant that interns apart from the plain constant with its bits.
bool isPlainConstant(const ASTNode& n);

// The number of values of a canonical index sort when it is at most 2^30,
// else 0. Only a chain over a sort this small can cover half of it.
uint64_t smallIndexCardinality(const SourceSort& index);

// Unsigned order on two constants of one width, by their bits.
bool constantBitsLess(const ASTNode& a, const ASTNode& b);

struct ConstantBitsLess
{
  bool operator()(const ASTNode& a, const ASTNode& b) const
  {
    return constantBitsLess(a, b);
  }
};

// The canonical form of the array that is `fill` everywhere, overwritten by
// `stores` in order (a later store at an index winning): `fill` becomes its
// default and `stores` its stores, ascending by index. The default changes
// only when it and every stored value are plain constants, as only then can
// the cells be counted. False, leaving both alone, unless `index` is a
// canonical index sort and every stored index a plain constant.
bool canonicaliseConstantArray(
    STPMgr& bm, const SourceSort& index, ASTNode& fill,
    std::vector<std::pair<ASTNode, ASTNode>>& stores);

// Whether `a` is a constant array with plain constant indexes, cells and
// default, bit-vector or Boolean cells, in the canonical form. Two such
// arrays are equal exactly when they are one node: the default is the most
// frequent cell value (by the tie-break when two are), and the stores are
// the cells that differ from it, in one order. Checks the whole form, so a
// chain the factory did not build answers too; one deeper than `budget`
// answers false.
bool isCanonicalConstantArray(const ASTNode& a, size_t budget = 4096);
} // namespace stp

#endif

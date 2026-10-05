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

#include "stp/AST/ArrayOps.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include <iterator>
#include <map>

namespace stp
{
namespace
{
bool bitIs(const ASTNode& n, unsigned value)
{
  return n.GetKind() == BVCONST && n.GetValueWidth() == 1 &&
         n.GetUnsignedConst() == value;
}
} // namespace

ASTNode booleanArrayRead(const ASTNode& value, bool negated)
{
  const bool hasNot = value.GetKind() == NOT;
  const ASTNode& equality = hasNot ? value[0] : value;
  if (equality.GetKind() != EQ || equality.Degree() != 2)
    return ASTNode();
  for (unsigned i = 0; i < 2; ++i)
  {
    const ASTNode& read = equality[i];
    if (read.GetKind() == READ &&
        bitIs(equality[1 - i], hasNot != negated ? 0 : 1) &&
        read[0].GetSourceSort().element().kind() == SourceSort::Kind::Bool)
      return read;
  }
  return ASTNode();
}

ASTNode packBoolean(NodeFactory& nf, const ASTNode& value)
{
  assert(value.GetType() == BOOLEAN_TYPE);
  if (value == nf.getTrue())
    return nf.CreateOneConst(1);
  if (value == nf.getFalse())
    return nf.CreateZeroConst(1);
  const ASTNode read = booleanArrayRead(value);
  if (!read.IsNull())
    return read;
  return nf.CreateTerm(ITE, 1, value, nf.CreateOneConst(1),
                       nf.CreateZeroConst(1));
}

ASTNode unpackBoolean(NodeFactory& nf, const ASTNode& bits)
{
  if (bits.GetType() == BOOLEAN_TYPE)
    return bits;
  assert(bits.GetValueWidth() == 1 && bits.GetIndexWidth() == 0);
  if (bits.GetKind() == BVCONST)
    return bitIs(bits, 0) ? nf.getFalse() : nf.getTrue();
  if (bits.GetKind() == ITE && bitIs(bits[1], 1) && bitIs(bits[2], 0))
    return bits[0];
  if (bits.GetKind() == ITE && bitIs(bits[1], 0) && bitIs(bits[2], 1))
    return nf.CreateNode(NOT, bits[0]);
  return nf.CreateNode(EQ, bits, nf.CreateOneConst(1));
}

ASTNode createArrayRead(NodeFactory& nf, const ASTNode& array,
                        const ASTNode& index)
{
  const SourceSort sort = array.GetSourceSort();
  assert(sort.kind() == SourceSort::Kind::Array);
  assert(index.GetSourceSort() == sort.index());
  const ASTNode packedIndex = sort.index().kind() == SourceSort::Kind::Bool
                                  ? packBoolean(nf, index)
                                  : index;
  const ASTNode read =
      nf.CreateTerm(READ, array.GetValueWidth(), array, packedIndex);
  return sort.element().kind() == SourceSort::Kind::Bool
             ? unpackBoolean(nf, read)
             : read;
}

ASTNode createArrayWrite(NodeFactory& nf, const ASTNode& array,
                         const ASTNode& index, const ASTNode& value)
{
  const SourceSort sort = array.GetSourceSort();
  assert(sort.kind() == SourceSort::Kind::Array);
  assert(index.GetSourceSort() == sort.index());
  assert(value.GetSourceSort() == sort.element());
  const ASTNode packedIndex = sort.index().kind() == SourceSort::Kind::Bool
                                  ? packBoolean(nf, index)
                                  : index;
  const ASTNode packedValue = sort.element().kind() == SourceSort::Kind::Bool
                                  ? packBoolean(nf, value)
                                  : value;
  return nf.CreateArrayTerm(WRITE, array.GetIndexWidth(), array.GetValueWidth(),
                            array, packedIndex, packedValue);
}

bool canonicalIndexSort(const SourceSort& index)
{
  return index.kind() == SourceSort::Kind::BitVector ||
         index.kind() == SourceSort::Kind::Bool;
}

bool isPlainConstant(const ASTNode& n)
{
  return n.GetKind() == BVCONST &&
         n.GetSourceSort().kind() == SourceSort::Kind::BitVector;
}

uint64_t smallIndexCardinality(const SourceSort& index)
{
  if (index.kind() == SourceSort::Kind::Bool)
    return 2;
  if (index.kind() == SourceSort::Kind::BitVector &&
      index.bitVectorWidth() <= 30)
    return uint64_t(1) << index.bitVectorWidth();
  return 0;
}

bool constantBitsLess(const ASTNode& a, const ASTNode& b)
{
  assert(a.GetKind() == BVCONST && b.GetKind() == BVCONST);
  assert(a.GetValueWidth() == b.GetValueWidth());
  return CONSTANTBV::BitVector_Lexicompare(a.GetBVConst(), b.GetBVConst()) < 0;
}

bool canonicaliseConstantArray(STPMgr& bm, const SourceSort& index,
                               ASTNode& fill,
                               std::vector<std::pair<ASTNode, ASTNode>>& stores)
{
  if (!canonicalIndexSort(index))
    return false;
  for (const auto& s : stores)
    if (!isPlainConstant(s.first))
      return false;

  // The last store at an index wins; a cell holding the default needs no
  // store.
  std::map<ASTNode, ASTNode, ConstantBitsLess> cells;
  for (const auto& s : stores)
    cells[s.first] = s.second;
  for (auto it = cells.begin(); it != cells.end();)
    it = (it->second == fill) ? cells.erase(it) : std::next(it);

  // Once the stores could cover half the sort the default must be the most
  // frequent cell value, which takes every value being a constant to count.
  const uint64_t card = smallIndexCardinality(index);
  bool countable =
      card != 0 && card <= 2 * (uint64_t)cells.size() && isPlainConstant(fill);
  for (const auto& c : cells)
    countable = countable && isPlainConstant(c.second);
  if (countable)
  {
    std::map<ASTNode, uint64_t, ConstantBitsLess> counts;
    counts[fill] = card - cells.size();
    for (const auto& c : cells)
      counts[c.second]++;
    ASTNode best = fill;
    for (const auto& c : counts)
      if (c.second > counts[best] ||
          (c.second == counts[best] && constantBitsLess(c.first, best)))
        best = c.first;
    if (best != fill)
    {
      const unsigned width = index.arrayComponentWidth();
      std::map<ASTNode, ASTNode, ConstantBitsLess> flipped;
      for (uint64_t k = 0; k < card; ++k)
      {
        const ASTNode at = bm.CreateBVConst(width, k);
        const auto it = cells.find(at);
        const ASTNode cell = (it == cells.end()) ? fill : it->second;
        if (cell != best)
          flipped[at] = cell;
      }
      cells.swap(flipped);
      fill = best;
    }
  }

  stores.assign(cells.begin(), cells.end());
  return true;
}

bool isCanonicalConstantArray(const ASTNode& a, size_t budget)
{
  const SourceSort sort = a.GetSourceSort();
  if (sort.kind() != SourceSort::Kind::Array ||
      !canonicalIndexSort(sort.index()))
    return false;
  const SourceSort::Kind element = sort.element().kind();
  if (element != SourceSort::Kind::BitVector &&
      element != SourceSort::Kind::Bool)
    return false;

  // Top down, so each index must be below the one above it.
  std::vector<ASTNode> values;
  ASTNode n = a;
  ASTNode above;
  while (n.GetKind() == WRITE)
  {
    if (values.size() == budget || !isPlainConstant(n[1]) ||
        !isPlainConstant(n[2]))
      return false;
    if (!above.IsNull() && !constantBitsLess(n[1], above))
      return false;
    above = n[1];
    values.push_back(n[2]);
    n = n[0];
  }
  if (n.GetKind() != CONST_ARRAY || !isPlainConstant(n[0]))
    return false;
  const ASTNode& fill = n[0];
  for (const ASTNode& v : values)
    if (v == fill)
      return false;

  const uint64_t card = smallIndexCardinality(sort.index());
  if (card != 0 && card <= 2 * (uint64_t)values.size())
  {
    std::map<ASTNode, uint64_t, ConstantBitsLess> counts;
    for (const ASTNode& v : values)
      counts[v]++;
    const uint64_t fillCount = card - values.size();
    for (const auto& c : counts)
      if (c.second > fillCount ||
          (c.second == fillCount && constantBitsLess(c.first, fill)))
        return false;
  }
  return true;
}
} // namespace stp

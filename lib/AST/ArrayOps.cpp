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
} // namespace stp

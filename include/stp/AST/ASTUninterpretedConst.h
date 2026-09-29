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

// An element of a sort introduced by declare-sort, as a value: the carrier
// pattern typed with its declared sort, so that a model value of such a sort
// is a term of that sort rather than a bare bit-vector. Kept as kind BVCONST
// like the RoundingMode and floating-point literals, and interned apart from
// the plain constant with the same bits through the declared source sort.

#ifndef ASTUNINTERPRETEDCONST_H
#define ASTUNINTERPRETEDCONST_H

#include "ASTBVConst.h"
#include "SourceSort.h"

namespace stp
{
class STPMgr;

class ASTUninterpretedConst final : public ASTBVConst
{
  friend class STPMgr;
  ASTUninterpretedConst(STPMgr* mgr, CBV bv, const SourceSort& sort);
  ASTUninterpretedConst(const ASTUninterpretedConst& other);
  SourceSort getDeclaredSourceSort() const override { return sort_; }
  const SourceSort sort_;

public:
  ~ASTUninterpretedConst() override = default;
};
} // namespace stp

#endif

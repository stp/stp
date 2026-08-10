/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: January 2021
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

#ifndef ASTFPCONST_H
#define ASTFPCONST_H

#include "ASTBVConst.h"

namespace stp
{
class STPMgr;

// A bitvector constant that additionally carries a floating-point format.
// Interned in the same unique table as plain bitvector constants: the
// table's equality functor compares the format widths as well as the bits,
// so 1.0f can never unify with the plain 32-bit pattern 0x3F800000, nor
// with the same bits read at a different format.
class ASTFPConst : public ASTBVConst
{
  friend class STPMgr;

  uint32_t _sig_width;
  uint32_t _exp_width;

  // The format is part of the node's identity in the unique table, so it is
  // fixed at construction. The setters only accept the stored value, in the
  // style of ASTBVConst::setValueWidth.
  void setSigWidth([[maybe_unused]] uint32_t sw) override
  {
    assert(sw == _sig_width);
  }
  uint32_t getSigWidth() const override { return _sig_width; }

  void setExpWidth([[maybe_unused]] uint32_t ew) override
  {
    assert(ew == _exp_width);
  }
  uint32_t getExpWidth() const override { return _exp_width; }

  SourceSort getDeclaredSourceSort() const override
  {
    return SourceSort::floatingPoint(_exp_width, _sig_width);
  }

  // Temporary-key constructor: shares `bv` without cloning or freeing it.
  ASTFPConst(STPMgr* mgr, CBV bv, uint32_t exp_width, uint32_t sig_width);

  // Copying constructor, used when interning a temporary key: clones the CBV.
  ASTFPConst(const ASTFPConst& other);

public:
  virtual ~ASTFPConst() {}
};

} // namespace stp
#endif

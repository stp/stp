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

//Class to represent internals of a bitvector constant
class ASTFPConst : public ASTBVConst
{
  uint32_t _sig_width;
  uint32_t _exp_width;

  virtual void setSigWidth(uint32_t sw) { _sig_width = sw; }
  virtual uint32_t getSigWidth() const { return _sig_width; }

  virtual void setExpWidth(uint32_t ew) { _exp_width = ew; }
  virtual uint32_t getExpWidth() const { return _exp_width; }

public:
  ASTFPConst(const ASTBVConst& n);
  virtual ~ASTFPConst() {}
};

} // namespace stp
#endif

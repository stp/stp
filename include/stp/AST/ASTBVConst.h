/********************************************************************
 *
 * BEGIN DATE: November, 2005
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

#ifndef ASTBVCONST_H
#define ASTBVCONST_H

#include "ASTInternal.h"

namespace stp
{
class STPMgr;

//Class to represent internals of a bitvector constant
class ASTBVConst : public ASTInternal
{
  friend class STPMgr;
  friend class ASTNode;
  friend class ASTNodeHasher;
  friend class ASTNodeEqual;

private:
  // CBV is actually an unsigned*. The bitvector constant is
  // represented using an external library in extlib-bvconst.
  CBV _bvconst;

  //Hasher for ASTBVConst nodes
  class ASTBVConstHasher
  {
  public:
    size_t operator()(const ASTBVConst* bvc) const;
  };

  //Equality for ASTBVConst nodes
  class ASTBVConstEqual
  {
  public:
    bool operator()(const ASTBVConst* bvc1, const ASTBVConst* bvc2) const;
  };

  ASTBVConst(CBV bv, unsigned int width);
  ASTBVConst(STPMgr* mgr, CBV bv, unsigned int /*width*/,
             bool managed_outside = false)
      : ASTInternal(mgr, BVCONST)
  {
    if (managed_outside)
    {
      _bvconst = (bv);
    }
    else
    {
      _bvconst = CONSTANTBV::BitVector_Clone(bv);
    }
    cbv_managed_outside = managed_outside;
  }

  ASTBVConst(const ASTBVConst& sym);

  // friend equality operator
  friend bool operator==(const ASTBVConst& bvc1, const ASTBVConst& bvc2)
  {
    if (bvc1.getValueWidth() != bvc2.getValueWidth())
      return false;
    return (0 == CONSTANTBV::BitVector_Compare(bvc1._bvconst, bvc2._bvconst));
  }

  // Call this when deleting a node that has been stored in the the
  // unique table
  virtual void CleanUp();

  // Print function for bvconst -- return _bvconst value in bin
  // format (c_friendly is for printing hex. numbers that C
  // compilers will accept)
  virtual void nodeprint(ostream& os, bool c_friendly = false);

  const static ASTVec astbv_empty_children;

  void setIndexWidth(uint32_t i) { assert(i == 0); }
  uint32_t getIndexWidth() const { return 0; }

  void setValueWidth(uint32_t v) { assert(v == getValueWidth()); }
  uint32_t getValueWidth() const { return bits_(_bvconst); }

public:
  virtual ASTVec const& GetChildren() const { return astbv_empty_children; }

  virtual ~ASTBVConst()
  {
    if (!cbv_managed_outside)
      CONSTANTBV::BitVector_Destroy(_bvconst);
  }

  // Return the bvconst. It is a const-value
  CBV GetBVConst() const;
};

} // end of namespace
#endif

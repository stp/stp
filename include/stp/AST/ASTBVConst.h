/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
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
  friend class ASTFPConst;
  friend class ASTRMConst;

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
    if (bvc1.getDeclaredSourceSort() != bvc2.getDeclaredSourceSort())
      return false;
    return (0 == CONSTANTBV::BitVector_Compare(bvc1._bvconst, bvc2._bvconst));
  }

  // Call this when deleting a node that has been stored in the the
  // unique table
  void CleanUp() override;

  // Print function for bvconst -- return _bvconst value in bin
  // format (c_friendly is for printing hex. numbers that C
  // compilers will accept)
  void nodeprint(ostream& os, bool c_friendly = false) override;

  const static ASTVec astbv_empty_children;

  void setIndexWidth([[maybe_unused]] uint32_t i) override { assert(i == 0); }
  uint32_t getIndexWidth() const override { return 0; }

  void setValueWidth([[maybe_unused]] uint32_t v) override
  {
    assert(v == getValueWidth());
  }
  uint32_t getValueWidth() const override { return bits_(_bvconst); }

  void setExpWidth(uint32_t) override { assert(false); }
  uint32_t getExpWidth() const override { return 0; }

  void setSigWidth(uint32_t) override { assert(false); }
  uint32_t getSigWidth() const override { return 0; }

  SourceSort getDeclaredSourceSort() const override
  {
    return SourceSort::bitVector(getValueWidth());
  }

public:
  ASTChildren GetChildren() const override { return astbv_empty_children; }

  virtual ~ASTBVConst()
  {
    if (!cbv_managed_outside)
      CONSTANTBV::BitVector_Destroy(_bvconst);
  }

  // Return the bvconst. It is a const-value
  CBV GetBVConst() const;
};

// Defined out of line because they dereference ASTBVConst, which is still
// incomplete inside the nested class bodies above.  They must stay in the
// header: they key STPMgr's bvconst unique table, so they run on every
// hash-cons probe, and being inline keeps that path free of a call.
inline size_t
ASTBVConst::ASTBVConstHasher::operator()(const ASTBVConst* bvc) const
{
  return CONSTANTBV::BitVector_Hash(bvc->_bvconst) ^
         (bvc->getDeclaredSourceSort().hash() * 0x9e3779b97f4a7c15ULL);
}

inline bool
ASTBVConst::ASTBVConstEqual::operator()(const ASTBVConst* bvc1,
                                        const ASTBVConst* bvc2) const
{
  if (bvc1->getDeclaredSourceSort() != bvc2->getDeclaredSourceSort())
  {
    return false;
  }
  return (0 == CONSTANTBV::BitVector_Compare(bvc1->_bvconst, bvc2->_bvconst));
}

} // end of namespace
#endif

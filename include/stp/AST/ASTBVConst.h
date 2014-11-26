// -*- c++ -*-
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
namespace BEEV
{
class STPMgr;

/******************************************************************
 *  Class ASTBVConst:                                             *
 *                                                                *
 *  Class to represent internals of a bitvector constant          *
 ******************************************************************/
class ASTBVConst : public ASTInternal
{
  friend class STPMgr;
  friend class ASTNode;
  friend class ASTNodeHasher;
  friend class ASTNodeEqual;

private:
  /****************************************************************
   * Private Data                                                 *
   ****************************************************************/

  // CBV is actually an unsigned*. The bitvector constant is
  // represented using an external library in extlib-bvconst.
  CBV _bvconst;

  // If the CBV is managed outside of this class. Then a defensive copy isn't
  // taken.
  bool cbv_managed_outside;

  /****************************************************************
   * Class ASTBVConstHasher:                                      *
   *                                                              *
   * Hasher for ASTBVConst nodes                                  *
   ****************************************************************/
  class ASTBVConstHasher
  {
  public:
    size_t operator()(const ASTBVConst* bvc) const;
  }; // End of class ASTBVConstHahser

  /****************************************************************
   * Class ASTBVConstEqual:                                       *
   *                                                              *
   * Equality for ASTBVConst nodes                                *
   ****************************************************************/
  class ASTBVConstEqual
  {
  public:
    bool operator()(const ASTBVConst* bvc1, const ASTBVConst* bvc2) const;
  }; // End of class ASTBVConstEqual

  /****************************************************************
   * Private Functions (virtual defs and friends)                 *
   ****************************************************************/

  // Constructor
  ASTBVConst(CBV bv, unsigned int width);

  enum CBV_LIFETIME
  {
    CBV_MANAGED_OUTSIDE
  };

  ASTBVConst(CBV bv, unsigned int width, enum CBV_LIFETIME l)
      : ASTInternal(BVCONST)
  {
    _bvconst = (bv);
    _value_width = width;
    cbv_managed_outside = true;
  }

  // Copy constructor.
  ASTBVConst(const ASTBVConst& sym);

  // friend equality operator
  friend bool operator==(const ASTBVConst& bvc1, const ASTBVConst& bvc2)
  {
    if (bvc1._value_width != bvc2._value_width)
      return false;
    return (0 == CONSTANTBV::BitVector_Compare(bvc1._bvconst, bvc2._bvconst));
  } // End of operator==

  // Call this when deleting a node that has been stored in the the
  // unique table
  virtual void CleanUp();

  // Print function for bvconst -- return _bvconst value in bin
  // format (c_friendly is for printing hex. numbers that C
  // compilers will accept)
  virtual void nodeprint(ostream& os, bool c_friendly = false);

  const static ASTVec astbv_empty_children;

public:
  virtual ASTVec const& GetChildren() const { return astbv_empty_children; }

  /****************************************************************
   * Public Member Functions                                      *
   ****************************************************************/

  // Destructor. Call the external destructor
  virtual ~ASTBVConst()
  {
    if (!cbv_managed_outside)
      CONSTANTBV::BitVector_Destroy(_bvconst);
  } // End of destructor

  // Return the bvconst. It is a const-value
  CBV GetBVConst() const;
}; // End of ASTBVConst
} // end of namespace
#endif

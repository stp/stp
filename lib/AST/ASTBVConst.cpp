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

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"

namespace stp
{
const ASTVec ASTBVConst::astbv_empty_children;

ASTBVConst::ASTBVConst(const ASTBVConst& sym)
    : ASTInternal(sym.nodeManager, sym._kind)
{
  _bvconst = CONSTANTBV::BitVector_Clone(sym._bvconst);
  cbv_managed_outside = false;
}

// Call this when deleting a node that has been stored in the the
// unique table
void ASTBVConst::CleanUp()
{
  nodeManager->_bvconst_unique_table.erase(this);
  delete this;
}

// The value in hex (0x...) when its width is a multiple of four, else in
// binary (0b...), as C writes them.
void ASTBVConst::nodeprint(ostream& os)
{
  unsigned char* res;
  const char* prefix;

  if (getValueWidth() % 4 == 0)
  {
    res = CONSTANTBV::BitVector_to_Hex(_bvconst);
    prefix = "0x";
  }
  else
  {
    res = CONSTANTBV::BitVector_to_Bin(_bvconst);
    prefix = "0b";
  }
  if (NULL == res)
  {
    os << "nodeprint: BVCONST : could not convert to string" << _bvconst;
    FatalError("");
  }
  os << prefix << res;
  CONSTANTBV::BitVector_Dispose(res);
}

CBV ASTBVConst::GetBVConst() const
{
  return _bvconst;
}

// ASTBVConstHasher::operator() and ASTBVConstEqual::operator() are defined
// inline in ASTBVConst.h.

} //end of namespace

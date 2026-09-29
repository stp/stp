/********************************************************************
 * AUTHORS: Vijay Ganesh
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

#include "stp/Printer/printers.h"
#include <cstdint>

namespace stp
{
using std::cout;
using std::endl;

/******************************************************************
 * Assorted print routines collected in one place. The code here is
 * different from the one in printers directory. It is possible that
 * there is some duplication.
 *
 * FIXME: Get rid of any redundant code
 ******************************************************************/

ostream& ASTNode::LispPrint(ostream& os, int indentation) const
{
  return printer::Lisp_Print(os, *this, indentation);
}

ostream& ASTNode::LispPrint_indent(ostream& os, int indentation) const
{
  return printer::Lisp_Print_indent(os, *this, indentation);
}

ostream& ASTNode::PL_Print(ostream& os, STPMgr* mgr, int indentation) const
{
  return printer::PL_Print(os, *this, mgr, indentation);
}

void lpvec(const ASTVec& vec)
{
  LispPrintVec(cout, vec, 0);
  cout << endl;
}

} // end of namespace stp

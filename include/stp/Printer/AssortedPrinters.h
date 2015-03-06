// -*- c++ -*-
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

#ifndef PRINTER_H
#define PRINTER_H

#include "stp/AST/AST.h"
namespace stp
{

/***************************************************************************
Class LispPrinter:  iomanipulator for printing ASTNode or ASTVec
***************************************************************************/
class LispPrinter
{

public:
  ASTNode _node;

  // number of spaces to print before first real character of
  // object.
  int _indentation;

  // FIXME: pass ASTNode by reference
  // Constructor to build the LispPrinter object
  LispPrinter(ASTNode node, int indentation)
      : _node(node), _indentation(indentation)
  {
  }

  friend ostream& operator<<(ostream& os, const LispPrinter& lp)
  {
    return lp._node.LispPrint(os, lp._indentation);
  };

}; 

// global function which accepts an integer and looks up the
// corresponding ASTNode and prints a string of that ASTNode
void Convert_MINISATVar_To_ASTNode_Print(int minisat_var, int decision,
                                         int polarity = 0);

void print_STPInput_Back(const ASTNode& query);
} // end of namespace stp
#endif

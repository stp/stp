/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
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

#ifndef PRINTERS_H_
#define PRINTERS_H_
#include <iostream>
#include <vector>
#include <cstring>

#include "stp/AST/AST.h"
#include "stp/AST/ASTKind.h"
#include "stp/STPManager/STP.h"
#include "stp/Util/Attributes.h"

namespace printer
{
using std::ostream;
DLL_PUBLIC ostream& Dot_Print(ostream& os, const stp::ASTNode n);
DLL_PUBLIC ostream& C_Print(ostream& os, const stp::ASTNode n, STPMgr *, const int indentation = 0);
DLL_PUBLIC ostream& PL_Print(ostream& os, const stp::ASTNode& n,  STPMgr* bm, int indentation = 0);
DLL_PUBLIC void PL_Print1(ostream& os, const ASTNode& n, int indentation, bool letize, STPMgr* bm );

ostream& Lisp_Print(ostream& os, const stp::ASTNode& n, int indentation = 0);
extern stp::ASTNodeSet Lisp_AlreadyPrintedSet;
ostream& Lisp_Print_indent(ostream& os, const stp::ASTNode& n,
                           int indentation = 0);

// The "PrintBack" functions also define all the variables that are used.
DLL_PUBLIC void SMTLIB1_PrintBack(ostream& os, const stp::ASTNode& n, STPMgr * mgr);
DLL_PUBLIC void SMTLIB2_PrintBack(ostream& os, const ASTNode& n, STPMgr *stp, bool definately_bv = false);

void outputBitVecSMTLIB2(const ASTNode n, ostream& os);

DLL_PUBLIC ostream& GDL_Print(ostream& os, const stp::ASTNode n);
DLL_PUBLIC ostream& GDL_Print(ostream& os, const ASTNode n, std::string (*annotate)(const ASTNode&));

ostream& Bench_Print(ostream& os, const ASTNode n);
}

#endif /* PRINTERS_H_ */

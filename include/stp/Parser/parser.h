/********************************************************************
 * AUTHORS: Vijay Ganesh, Felix Kutzner
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

#ifndef PARSER_H
#define PARSER_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/Attributes.h"
#include <cstdio>

namespace stp
{
// external parser table for declared symbols.
// extern ASTNodeSet _parser_symbol_table;

// Symbols in generated  files used by tools/stp
void SMTScanString(const char* yy_str);
void SMT2ScanString(const char* yy_str);
void CVCScanString(const char* yy_str);
DLL_PUBLIC FILE* getCVCIn();
DLL_PUBLIC FILE* getSMTIn();
DLL_PUBLIC FILE* getSMT2In();
DLL_PUBLIC void setCVCIn(FILE* file);
DLL_PUBLIC void setSMTIn(FILE* file);
DLL_PUBLIC void setSMT2In(FILE* file);

DLL_PUBLIC int SMTParse(void* AssertsQuery);
DLL_PUBLIC int SMT2Parse();
DLL_PUBLIC int CVCParse(void* AssertsQuery);
} // end of namespace

DLL_PUBLIC int cvclex_destroy(void);
DLL_PUBLIC int smtlex_destroy(void);
DLL_PUBLIC int smt2lex_destroy(void);

#endif

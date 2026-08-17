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
#include <cstring>
#include <iostream>
#include <vector>

#include "stp/AST/AST.h"
#include "stp/AST/ASTKind.h"
#include "stp/STPManager/STP.h"
#include "stp/Util/Attributes.h"

namespace printer
{
using std::ostream;

// State for the letize pass, which walks a node and gives a let variable to
// every non-atomic subterm that occurs more than once. Each printer keeps its
// own storage for the result -- the SMT-LIB printers use file-scope
// thread-locals, the Presentation Language printer uses STPMgr members -- so
// the pass borrows it rather than owning it.
struct LetizeState
{
  // Subterms already visited.
  stp::ASTNodeSet& seen;
  // Subterm -> the let variable standing for it.
  stp::ASTNodeMap& letVarMap;
  // The same pairs, in creation order, so the bindings print in a stable order.
  vector<std::pair<stp::ASTNode, stp::ASTNode>>& letVarVec;
  // Name prefix for the generated variables.
  const char* prefix;
};

void LetizeNode(const stp::ASTNode& n, LetizeState& st, STPMgr*);

DLL_PUBLIC ostream& Dot_Print(ostream& os, const stp::ASTNode n);
DLL_PUBLIC ostream& PL_Print(ostream& os, const stp::ASTNode& n, STPMgr* bm,
                             int indentation = 0);
DLL_PUBLIC void PL_Print1(ostream& os, const ASTNode& n, int indentation,
                          bool letize, STPMgr* bm);

ostream& Lisp_Print(ostream& os, const stp::ASTNode& n, int indentation = 0);
extern THREAD_LOCAL_IE stp::ASTNodeSet Lisp_AlreadyPrintedSet;
ostream& Lisp_Print_indent(ostream& os, const stp::ASTNode& n,
                           int indentation = 0);

// The "PrintBack" functions also define all the variables that are used.
DLL_PUBLIC void SMTLIB2_PrintBack(ostream& os, const ASTNode& n, STPMgr* stp,
                                  bool definately_bv = false);

// Prints just the expression, without the declarations that the "PrintBack"
// functions emit. Used by get-assertions, which must print the asserted
// formulas alone.
DLL_PUBLIC void SMTLIB2_Print1(ostream& os, const stp::ASTNode n,
                               int indentation, bool letize);

// Emitters for a BVCONST (or a BITVECTOR wrapping one).
void outputBitVecSMTLIB2(const ASTNode n, ostream& os);
void outputFloatingPointSMTLIB2(const ASTNode n, ostream& os,
                                const ASTNode term);
void outputFloatingPointSMTLIB2(const ASTNode n, ostream& os,
                                unsigned int exp_width,
                                unsigned int sig_width);

// The SMT-LIB short name (RNE...) for a one-hot rounding-mode encoding
// (see symbolic_fp's rounding_modes), or NULL when the value names no mode.
const char* roundingModeName(unsigned encoding);

DLL_PUBLIC ostream& GDL_Print(ostream& os, const stp::ASTNode n);
DLL_PUBLIC ostream& GDL_Print(ostream& os, const ASTNode n,
                              std::string (*annotate)(const ASTNode&));
}

#endif /* PRINTERS_H_ */

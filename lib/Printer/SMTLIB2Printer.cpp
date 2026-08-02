/********************************************************************
 * AUTHORS: Trevor Hansen, Vijay Ganesh
 *
 * BEGIN DATE: July, 2009
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

#include "stp/Printer/SMTLIBPrinter.h"
#include "stp/Printer/printers.h"
#include <cassert>
#include <cctype>

// Outputs in the SMTLIB format. If you want something that can be parsed by
// other tools call
// SMTLIB_PrintBack(). SMTLIB_Print() prints just an expression.

namespace printer
{

using std::string;
using namespace stp;

void printVarDeclsToStream(ASTNodeSet& symbols, ostream& os);

void SMTLIB2_PrintBack(ostream& os, const ASTNode& n, STPMgr* mgr,
                       const bool definately_bv)
{
  if (!definately_bv && containsArrayOps(n, mgr))
    os << "(set-logic QF_ABV)\n";
  else
    os << "(set-logic QF_BV)\n";

  os << "(set-info :smt-lib-version 2.0)\n";

  if (input_status == TO_BE_SATISFIABLE)
  {
    os << "(set-info :status sat)\n";
  }
  else if (input_status == TO_BE_UNSATISFIABLE)
  {
    os << "(set-info :status unsat)\n";
  }
  else
    os << "(set-info :status unknown)\n";

  ASTNodeSet visited, symbols;
  buildListOfSymbols(n, visited, symbols);
  printVarDeclsToStream(symbols, os);
  os << "(assert ";
  SMTLIB_Print(os, mgr, n, 0, false);
  os << ")\n";
  // os << "(check-sat)" << endl;
  // os << "(exit)\n";
}

void printVarDeclsToStream(ASTNodeSet& symbols, ostream& os)
{
  for (ASTNodeSet::const_iterator i = symbols.begin(), iend = symbols.end();
       i != iend; i++)
  {
    const stp::ASTNode& a = *i;
    os << "(declare-fun ";

    // Should be a symbol.
    assert(a.GetKind() == SYMBOL);
    os << "|";
    a.nodeprint(os);
    os << "|";

    switch (a.GetType())
    {
      case stp::BITVECTOR_TYPE:
        os << " () (";
        os << "_ BitVec " << a.GetValueWidth() << ")";

        break;
      case stp::ARRAY_TYPE:
        os << " () (";
        os << "Array (_ BitVec " << a.GetIndexWidth() << ") (_ BitVec "
           << a.GetValueWidth() << ") )";
        break;
      case stp::BOOLEAN_TYPE:
        os << " () Bool ";
        break;
      default:
        stp::FatalError("printVarDeclsToStream: Unsupported type", a);
        break;
    }
    os << ")\n";
  }
} // printVarDeclsToStream

void outputBitVecSMTLIB2(const ASTNode n, ostream& os)
{
  const Kind k = n.GetKind();
  const ASTChildren c = n.GetChildren();
  ASTNode op;

  if (BITVECTOR == k)
  {
    op = c[0];
  }
  else if (BVCONST == k)
  {
    op = n;
  }
  else
    FatalError("nsadfsdaf");

  // CONSTANTBV::BitVector_to_Dec is very slow on 30,000 bits because it does lots of divisions.

  if (op.GetValueWidth() % 4 == 0)
  {
    os << " #x";
    unsigned char* str = CONSTANTBV::BitVector_to_Hex(n.GetBVConst());
    os << str;
    CONSTANTBV::BitVector_Dispose(str);
  }
  else
  {
    os << " #b";
    unsigned char* str = CONSTANTBV::BitVector_to_Bin(n.GetBVConst());
    os << str;
    CONSTANTBV::BitVector_Dispose(str);
  }
}

// Thin wrapper over the shared traversal. Declared in printers.h because
// get-assertions prints the asserted formulas through it.
void SMTLIB2_Print1(ostream& os, const ASTNode n, int indentation, bool letize)
{
  SMTLIB_Print1(os, n, indentation, letize, false);
}
}

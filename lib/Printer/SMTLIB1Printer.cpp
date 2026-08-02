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

// Outputs in the SMTLIB1 format. If you want something that can be parsed by
// other tools call
// SMTLIB_PrintBack(). SMTLIB_Print() prints just an expression.
// Wierdly is seems that only terms, not formulas can be LETized.

// NB: This code doesn't include the substitution map. So if you've already
// simplified
// the graph, then solving what this prints out wont necessarily give you a
// model.

namespace printer
{
using std::string;
using std::endl;
using namespace stp;

void printSMTLIB1VarDeclsToStream(ASTNodeSet& symbols, ostream& os);

void SMTLIB1_PrintBack(ostream& os, const ASTNode& n, STPMgr* mgr)
{
  os << "(" << endl;
  os << "benchmark blah" << endl;
  if (containsArrayOps(n, mgr))
    os << ":logic QF_AUFBV" << endl;
  else
    os << ":logic QF_BV" << endl;

  if (input_status == TO_BE_SATISFIABLE)
  {
    os << ":status sat" << endl;
  }
  else if (input_status == TO_BE_UNSATISFIABLE)
  {
    os << ":status unsat" << endl;
  }
  else
    os << ":status unknown" << endl;

  ASTNodeSet visited, symbols;
  buildListOfSymbols(n, visited, symbols);
  printSMTLIB1VarDeclsToStream(symbols, os);
  os << ":formula ";
  SMTLIB_Print(os, mgr, n, 0, true);
  os << ")" << endl;
}

void printSMTLIB1VarDeclsToStream(ASTNodeSet& symbols, ostream& os)
{
  for (ASTNodeSet::const_iterator i = symbols.begin(), iend = symbols.end();
       i != iend; i++)
  {
    const stp::ASTNode& a = *i;

    // Should be a symbol.
    assert(a.GetKind() == SYMBOL);

    switch (a.GetType())
    {
      case stp::BITVECTOR_TYPE:

        os << ":extrafuns (( ";
        a.nodeprint(os);
        os << " BitVec[" << a.GetValueWidth() << "]";
        os << " ))" << endl;
        break;
      case stp::ARRAY_TYPE:
        os << ":extrafuns (( ";
        a.nodeprint(os);
        os << " Array[" << a.GetIndexWidth();
        os << ":" << a.GetValueWidth() << "] ))" << endl;
        break;
      case stp::BOOLEAN_TYPE:
        os << ":extrapreds (( ";
        a.nodeprint(os);
        os << "))" << endl;
        break;
      default:
        stp::FatalError("printVarDeclsToStream: Unsupported type", a);
        break;
    }
  }
} // printVarDeclsToStream

void outputBitVec(const ASTNode n, ostream& os)
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
    FatalError("nsadfsdaf2");

  // CONSTANTBV::BitVector_to_Dec returns a signed representation by default.
  // Prepend with zero to convert to unsigned.

  os << "bv";
  CBV zero = CONSTANTBV::BitVector_Create(1, true);
  CBV unsign = CONSTANTBV::BitVector_Concat(zero, op.GetBVConst());
  unsigned char* str = CONSTANTBV::BitVector_to_Dec(unsign);
  CONSTANTBV::BitVector_Destroy(unsign);
  CONSTANTBV::BitVector_Destroy(zero);
  os << str << "[" << op.GetValueWidth() << "]";
  CONSTANTBV::BitVector_Dispose(str);
}

}

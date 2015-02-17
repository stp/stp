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
#include "stp/Printer/AssortedPrinters.h"

// to get the PRIu64 macro from inttypes, this needs to be defined.
#include <inttypes.h>
//#undef __STDC_FORMAT_MACROS

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

ostream& ASTNode::PL_Print(ostream& os, int indentation) const
{
  return printer::PL_Print(os, *this, indentation);
}

// This is the IO manipulator.  It builds an object of class
//"LispPrinter" that has a special overloaded "<<" operator.
inline LispPrinter lisp(const ASTNode& node, int indentation = 0)
{
  LispPrinter lp(node, indentation);
  return lp;
} // end of LispPrinter_lisp

// FIXME: Made non-ref in the hope that it would work better.
void lp(ASTNode node)
{
  cout << lisp(node) << endl;
}

void lpvec(const ASTVec& vec)
{
  LispPrintVec(cout, vec, 0);
  cout << endl;
}

//  //Variable Order Printer: A global function which converts a MINISAT
//   //var into a ASTNODE var. It then prints this var along with
//   //variable order dcisions taken by MINISAT.
//   void Convert_MINISATVar_To_ASTNode_Print(int minisat_var,
//                                       int decision_level, int polarity)
//   {
//     stp::ASTNode vv = stp::GlobalSTPMgr->_SATVar_to_AST[minisat_var];
//     cout << spaces(decision_level);
//     if (polarity)
//       {
//         cout << "!";
//       }
//     printer::PL_Print(cout,vv, 0);
//     cout << endl;
//   } //end of Convert_MINISATVar_To_ASTNode_Print()

void STPMgr::printVarDeclsToStream(ostream& os, ASTNodeSet& ListOfDeclaredVars)
{
  for (ASTNodeSet::iterator i = ListOfDeclaredVars.begin(),
                            iend = ListOfDeclaredVars.end();
       i != iend; i++)
  {
    stp::ASTNode a = *i;
    switch (a.GetType())
    {
      case stp::BITVECTOR_TYPE:
        a.PL_Print(os);
        os << " : BITVECTOR(" << a.GetValueWidth() << ");" << endl;
        break;
      case stp::ARRAY_TYPE:
        a.PL_Print(os);
        os << " : ARRAY "
           << "BITVECTOR(" << a.GetIndexWidth() << ") OF ";
        os << "BITVECTOR(" << a.GetValueWidth() << ");" << endl;
        break;
      case stp::BOOLEAN_TYPE:
        a.PL_Print(os);
        os << " : BOOLEAN;" << endl;
        break;
      default:
        stp::FatalError("vc_printDeclsToStream: Unsupported type", a);
        break;
    }
  }
} // printVarDeclsToStream

void STPMgr::printAssertsToStream(ostream& os, int simplify_print)
{
  ASTVec v = GetAsserts();
  for (ASTVec::iterator i = v.begin(), iend = v.end(); i != iend; i++)
  {
    // Begin_RemoveWrites = true; ASTNode q = (simplify_print == 1) ?
    // SimplifyFormula_TopLevel(*i,false) : *i; q = (simplify_print
    //== 1) ? SimplifyFormula_TopLevel(q,false) : q;
    ASTNode q = *i;
    // Begin_RemoveWrites = false;
    os << "ASSERT( ";
    q.PL_Print(os);
    os << ");" << endl;
  }
}

void print_STPInput_Back(const ASTNode& query)
{

  // Determine the symbols in the query and asserts.
  ASTNodeSet visited;
  ASTNodeSet symbols;
  buildListOfSymbols(query, visited, symbols);
  ASTVec v = (stp::GlobalSTP->bm)->GetAsserts();
  for (ASTVec::iterator i = v.begin(), iend = v.end(); i != iend; i++)
    buildListOfSymbols(*i, visited, symbols);

  (stp::GlobalSTP->bm)->printVarDeclsToStream(cout, symbols);
  (stp::GlobalSTP->bm)->printAssertsToStream(cout, 0);
  cout << "QUERY(";
  query.PL_Print(cout);
  cout << ");\n";
} // end of print_STPInput_Back()
} // end of namespace stp

/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, David L. Dill
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

namespace printer
{

using std::string;
using std::endl;
using namespace stp;

string functionToCVCName(const Kind k)
{
  switch (k)
  {

    case BVUMINUS:
    case NOT:
    case BVLT:
    case BVLE:
    case BVGT:
    case BVGE:
    case BVXOR:
    case BVNAND:
    case BVNOR:
    case BVXNOR:
    case BVMULT:
    case AND:
    case OR:
    case NAND:
    case NOR:
    case XOR:
    case BVSUB:
    case BVPLUS:
    case SBVDIV:
    case SBVREM:
    case SBVMOD:
    case BVDIV:
    case BVMOD:
      return _kind_names[k];
      break;
    case BVSLT:
      return "SBVLT";
    case BVSLE:
      return "SBVLE";
    case BVSGT:
      return "SBVGT";
    case BVSGE:
      return "SBVGE";
    case IFF:
      return "<=>";
    case IMPLIES:
      return "=>";
    case BVNOT:
      return "~";
    case EQ:
      return "=";
    case BVCONCAT:
      return "@";
    case BVOR:
      return "|";
    case BVAND:
      return "&";
    default:
    {
      std::cerr << "Unknown name when outputting:";
      FatalError(_kind_names[k]);
      return ""; // to quieten compiler/
    }
  }
}

void PL_Print1(ostream& os, const ASTNode& n, int indentation, bool letize,
               STPMgr* bm)
{
  // os << spaces(indentation);
  // os << endl << spaces(indentation);
  if (!n.IsDefined())
  {
    os << "<undefined>";
    return;
  }

  // this is to print letvars for shared subterms inside the printing
  // of "(LET v0 = term1, v1=term1@term2,...
  if ((bm->NodeLetVarMap1.find(n) != bm->NodeLetVarMap1.end()) && !letize)
  {
    PL_Print1(os, (bm->NodeLetVarMap1[n]), indentation, letize, bm);
    return;
  }

  // this is to print letvars for shared subterms inside the actual
  // term to be printed
  if ((bm->NodeLetVarMap.find(n) != bm->NodeLetVarMap.end()) && letize)
  {
    PL_Print1(os, (bm->NodeLetVarMap[n]), indentation, letize, bm);
    return;
  }

  // otherwise print it normally
  const Kind kind = n.GetKind();
  const ASTVec& c = n.GetChildren();
  switch (kind)
  {
    case BOOLEXTRACT:
      PL_Print1(os, c[0], indentation, letize, bm);
      os << "{";
      PL_Print1(os, c[1], indentation, letize, bm);
      os << "}";
      break;
    case BITVECTOR:
      os << "BITVECTOR(";
      unsigned char* str;
      str = CONSTANTBV::BitVector_to_Hex(c[0].GetBVConst());
      os << str << ")";
      CONSTANTBV::BitVector_Dispose(str);
      break;
    case BOOLEAN:
      os << "BOOLEAN";
      break;
    case FALSE:
    case TRUE:
      os << kind;
      break;
    case BVCONST:
    case SYMBOL:
      n.nodeprint(os, true);
      break;
    case READ:
      PL_Print1(os, c[0], indentation, letize, bm);
      os << "[";
      PL_Print1(os, c[1], indentation, letize, bm);
      os << "]";
      break;
    case WRITE:
      os << "(";
      PL_Print1(os, c[0], indentation, letize, bm);
      os << " WITH [";
      PL_Print1(os, c[1], indentation, letize, bm);
      os << "] := ";
      PL_Print1(os, c[2], indentation, letize, bm);
      os << ")";
      os << endl;
      break;
    case BVUMINUS:
    case NOT:
    case BVNOT:
      assert(1 == c.size());
      os << "( ";
      os << functionToCVCName(kind);
      os << "( ";
      PL_Print1(os, c[0], indentation, letize, bm);
      os << "))";
      break;
    case BVEXTRACT:
      PL_Print1(os, c[0], indentation, letize, bm);
      os << "[";
      os << c[1].GetUnsignedConst();
      os << ":";
      os << c[2].GetUnsignedConst();
      os << "]";
      break;
    case BVLEFTSHIFT:
      assert(2 == c.size());
      if (c[1].isConstant())
      {
        os << "(";
        PL_Print1(os, c[0], indentation, letize, bm);
        os << " << ";
        os << c[1].GetUnsignedConst();
        os << ")";
        os << "[";
        os << (c[0].GetValueWidth() - 1);
        os << " : "
           << "0]";
      }
      else
      {
        os << "BVSHL(";
        PL_Print1(os, c[0], indentation, letize, bm);
        os << ", ";
        PL_Print1(os, c[1], indentation, letize, bm);
        os << ")" << endl;
      }
      break;
    case BVRIGHTSHIFT:
      assert(2 == c.size());
      if (c[1].isConstant())
      {
        os << "(";
        PL_Print1(os, c[0], indentation, letize, bm);
        os << " << ";
        os << c[1].GetUnsignedConst();
        os << ")";
      }
      else
      {
        os << "BVLSHR(";
        PL_Print1(os, c[0], indentation, letize, bm);
        os << ", ";
        PL_Print1(os, c[1], indentation, letize, bm);
        os << ")" << endl;
      }
      break;
    case BVSRSHIFT:
      assert(2 == c.size());
      os << "BVASHR(";
      PL_Print1(os, c[0], indentation, letize, bm);
      os << ", ";
      PL_Print1(os, c[1], indentation, letize, bm);
      os << ")" << endl;
      break;

    case BVMULT: // variable arity, function name at front, size next, comma
                 // separated.
    case BVSUB:
    case BVPLUS:
    case SBVDIV:
    case SBVREM:
    case SBVMOD:
    case BVDIV:
    case BVMOD:
      os << functionToCVCName(kind) << "(";
      os << n.GetValueWidth();
      for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend;
           it++)
      {
        os << ", " << endl;
        PL_Print1(os, *it, indentation, letize, bm);
      }
      os << ")" << endl;
      break;
    case ITE:
      os << "IF(";
      PL_Print1(os, c[0], indentation, letize, bm);
      os << ")" << endl;
      os << "THEN ";
      PL_Print1(os, c[1], indentation, letize, bm);
      os << endl << "ELSE ";
      PL_Print1(os, c[2], indentation, letize, bm);
      os << endl << "ENDIF";
      break;
    case PARAMBOOL:
      PL_Print1(os, c[0], indentation, letize, bm);
      os << "(";
      PL_Print1(os, c[1], indentation, letize, bm);
      os << ")";
      break;

    case BVLT: // two arity, prefixed function name.
    case BVLE:
    case BVGT:
    case BVGE:
    case BVXOR:
    case BVNAND:
    case BVNOR:
    case BVXNOR:
    case BVSLT:
    case BVSLE:
    case BVSGT:
    case BVSGE:
      assert(2 == c.size());
      os << functionToCVCName(kind) << "(";
      PL_Print1(os, c[0], indentation, letize, bm);
      os << ",";
      PL_Print1(os, c[1], indentation, letize, bm);
      os << ")" << endl;
      break;

    case BVCONCAT: // two arity, infix function name.
    case BVOR:
    case BVAND:
    case EQ:
    case IFF:
    case IMPLIES:
      assert(2 == c.size());
    // run on.
    case AND: // variable arity, infix function name.
    case OR:
    case NAND:
    case NOR:
    case XOR:
    {
      os << "(";
      PL_Print1(os, c[0], indentation, letize, bm);
      ASTVec::const_iterator it = c.begin();
      ASTVec::const_iterator itend = c.end();

      it++;
      for (; it != itend; it++)
      {
        os << " " << functionToCVCName(kind) << " ";
        PL_Print1(os, *it, indentation, letize, bm);
        os << endl;
      }
      os << ")";
      break;
    }
    case BVSX:
    case BVZX:
      os << kind << "(";
      PL_Print1(os, c[0], indentation, letize, bm);
      os << ",";
      os << n.GetValueWidth();
      os << ")" << endl;
      break;
    default:
      // remember to use LispPrinter here. Otherwise this function will
      // go into an infinite loop. Recall that "<<" is overloaded to
      // the lisp printer. FatalError uses lispprinter
      FatalError("PL_Print1: printing not implemented for this kind: ", n);
      break;
  }
}

// print in PRESENTATION LANGUAGE
//
// two pass algorithm:
//
// 1. In the first pass, letize this Node, N: i.e. if a node
// 1. appears more than once in N, then record this fact.
//
// 2. In the second pass print a "global let" and then print N
// 2. as follows: Every occurence of a node occuring more than
// 2. once is replaced with the corresponding let variable.
ostream& PL_Print(ostream& os, const ASTNode& n, STPMgr* bm, int indentation)
{
  // Clear the PrintMap
  bm->PLPrintNodeSet.clear();
  bm->NodeLetVarMap.clear();
  bm->NodeLetVarVec.clear();
  bm->NodeLetVarMap1.clear();

  // pass 1: letize the node
  n.LetizeNode(bm);

  // pass 2:
  //
  // 2. print all the let variables and their counterpart expressions
  // 2. as follows (LET var1 = expr1, var2 = expr2, ...
  //
  // 3. Then print the Node itself, replacing every occurence of
  // 3. expr1 with var1, expr2 with var2, ...
  // os << "(";
  if (0 < bm->NodeLetVarMap.size())
  {
    // ASTNodeMap::iterator it=bm->NodeLetVarMap.begin();
    // ASTNodeMap::iterator itend=bm->NodeLetVarMap.end();
    vector<std::pair<ASTNode, ASTNode>>::iterator it =
        bm->NodeLetVarVec.begin();
    vector<std::pair<ASTNode, ASTNode>>::iterator itend =
        bm->NodeLetVarVec.end();

    os << "(LET ";
    // print the let var first
    PL_Print1(os, it->first, indentation, false, bm);
    os << " = ";
    // print the expr
    PL_Print1(os, it->second, indentation, false, bm);

    // update the second map for proper printing of LET
    bm->NodeLetVarMap1[it->second] = it->first;

    for (it++; it != itend; it++)
    {
      os << "," << std::endl;
      // print the let var first
      PL_Print1(os, it->first, indentation, false, bm);
      os << " = ";
      // print the expr
      PL_Print1(os, it->second, indentation, false, bm);

      // update the second map for proper printing of LET
      bm->NodeLetVarMap1[it->second] = it->first;
    }

    os << " IN " << std::endl;
    PL_Print1(os, n, indentation, true, bm);
    os << ") ";
  }
  else
    PL_Print1(os, n, indentation, false, bm);
  // os << " )";
  os << " ";
  return os;
}
}

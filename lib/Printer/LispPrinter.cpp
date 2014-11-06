/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
 *
 * BEGIN DATE: November, 2005
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ********************************************************************/
// -*- c++ -*-

#include "stp/Printer/printers.h"

namespace printer
{

  using std::string;
  using namespace BEEV;

  ASTNodeSet Lisp_AlreadyPrintedSet;
  ostream &Lisp_Print_indent(ostream &os,  const ASTNode& n,int indentation);


  /** Internal function to print in lisp format.  Assume newline
      and indentation printed already before first line.  Recursive
      calls will have newline & indent, though */
  ostream &Lisp_Print1(ostream &os,  const ASTNode& n, int indentation)
  {
    if (!n.IsDefined())
      {
        os << "<undefined>";
        return os;
      }
    Kind kind = n.GetKind();
    // FIXME: figure out how to avoid symbols with same names as kinds.
    //    if (kind == READ) {
    //      const ASTVec &children = GetChildren();
    //      children[0].LispPrint1(os, indentation);
    //  os << "[" << children[1] << "]";
    //    } else
    if (kind == BOOLEXTRACT)
      {
        const ASTVec &children = n.GetChildren();
        // child 0 is a symbol.  Print without the NodeNum.
        os << n.GetNodeNum() << ":";

        children[0].nodeprint(os,true);
        os << "{";
        children[1].nodeprint(os,true);
        os << "}";
      }
    else if (kind == NOT)
      {
        const ASTVec &children = n.GetChildren();
        os << n.GetNodeNum() << ":";
        os << "(NOT ";
        Lisp_Print1(os,children[0], indentation);
        os << ")";
      }
    else if (n.Degree() == 0)
      {
        // Symbol or a kind with no children print as index:NAME if shared,
        // even if they have been printed before.
        os << n.GetNodeNum() << ":";
        n.nodeprint(os,true);
        // os << "(" << _int_node_ptr->_ref_count << ")";
        // os << "{" << GetValueWidth() << "}";
      }
    else if (Lisp_AlreadyPrintedSet.find(n) != Lisp_AlreadyPrintedSet.end())
      {
        // print non-symbols as "[index]" if seen before.
        os << "[" << n.GetNodeNum() << "]";
        //         << "(" << _int_node_ptr->_ref_count << ")";
      }
    else
      {
        Lisp_AlreadyPrintedSet.insert(n);
        const ASTVec &children = n.GetChildren();
        os << n.GetNodeNum() << ":"
          //<< "(" << _int_node_ptr->_ref_count << ")"
           << "(" << kind << " ";
        // os << "{" << GetValueWidth() << "}";
        ASTVec::const_iterator iend = children.end();
        for (ASTVec::const_iterator i = children.begin(); i != iend; i++)
          {
            Lisp_Print_indent(os, *i, indentation + 2);
          }
        os << ")";
      }
    return os;
  }

  // Print in lisp format
  ostream &Lisp_Print(ostream &os, const ASTNode& n,  int indentation)
  {
    // Clear the PrintMap
    Lisp_AlreadyPrintedSet.clear();
    Lisp_Print_indent(os, n, indentation);
    printf("\n");
    return os;
  }

  // Print newline and indentation, then print the thing.
  ostream &Lisp_Print_indent(ostream &os,  const ASTNode& n,int indentation)
  {
    os << std::endl << spaces(indentation);
    Lisp_Print1(os, n, indentation);
    return os;
  }

}

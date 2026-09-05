/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
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
#include <deque>
#include <utility>

namespace printer
{

using std::string;
using namespace stp;

THREAD_LOCAL_IE ASTNodeSet Lisp_AlreadyPrintedSet;
ostream& Lisp_Print_indent(ostream& os, const ASTNode& n, int indentation);

/** Internal function to print in lisp format.  Assume newline
    and indentation printed already before first line.  Recursive
    calls will have newline & indent, though */
/* The walk is iterative. How deeply a node nests is the input's choice, and
   printing is on the path an error message takes -- operator<< on a node
   comes through here -- so a formula too deep to print is a formula too deep
   to report on. Text that the recursion emitted after returning from a child
   is queued as a literal instead, so the output is unchanged.
   See DeepDag_Test.cpp. */
ostream& Lisp_Print1(ostream& os, const ASTNode& n, int indentation)
{
  // Either a node still to print, or text to emit once the nodes queued
  // after it are done. `indented` marks the children that the recursion
  // reached through Lisp_Print_indent, which puts them on their own line.
  struct Item
  {
    ASTNode n;
    int indentation = 0;
    bool indented = false;
    const char* literal = nullptr;
  };

  // A deque, so pushing never moves what is already queued.
  std::deque<Item> stack;
  stack.push_back(Item{n, indentation, false, nullptr});

  while (!stack.empty())
  {
    const Item item = std::move(stack.back());
    stack.pop_back();

    if (item.literal != nullptr)
    {
      os << item.literal;
      continue;
    }

    if (item.indented)
      os << std::endl << spaces(item.indentation);

    const ASTNode& current = item.n;

    if (!current.IsDefined())
    {
      os << "<undefined>";
      continue;
    }

    const Kind kind = current.GetKind();
    // FIXME: figure out how to avoid symbols with same names as kinds.
    if (kind == BOOLEXTRACT)
    {
      const ASTChildren children = current.GetChildren();
      // child 0 is a symbol.  Print without the NodeNum.
      os << current.GetNodeNum() << ":";

      children[0].nodeprint(os, true);
      os << "{";
      children[1].nodeprint(os, true);
      os << "}";
    }
    else if (kind == NOT)
    {
      const ASTChildren children = current.GetChildren();
      os << current.GetNodeNum() << ":";
      os << "(NOT ";
      stack.push_back(Item{ASTNode(), 0, false, ")"});
      stack.push_back(Item{children[0], item.indentation, false, nullptr});
    }
    else if (current.Degree() == 0)
    {
      // Symbol or a kind with no children print as index:NAME if shared,
      // even if they have been printed before.
      os << current.GetNodeNum() << ":";
      current.nodeprint(os, true);
    }
    else if (Lisp_AlreadyPrintedSet.find(current) !=
             Lisp_AlreadyPrintedSet.end())
    {
      // print non-symbols as "[index]" if seen before.
      os << "[" << current.GetNodeNum() << "]";
    }
    else
    {
      Lisp_AlreadyPrintedSet.insert(current);
      const ASTChildren children = current.GetChildren();
      os << current.GetNodeNum() << ":"
         << "(" << kind << " ";

      // Closing bracket first, so it comes off after every child.
      stack.push_back(Item{ASTNode(), 0, false, ")"});
      for (size_t i = children.size(); i > 0; i--)
        stack.push_back(
            Item{children[i - 1], item.indentation + 2, true, nullptr});
    }
  }

  return os;
}

// Print in lisp format
ostream& Lisp_Print(ostream& os, const ASTNode& n, int indentation)
{
  // Clear the PrintMap
  Lisp_AlreadyPrintedSet.clear();
  Lisp_Print_indent(os, n, indentation);
  printf("\n");
  return os;
}

// Print newline and indentation, then print the thing.
ostream& Lisp_Print_indent(ostream& os, const ASTNode& n, int indentation)
{
  os << std::endl << spaces(indentation);
  Lisp_Print1(os, n, indentation);
  return os;
}
}

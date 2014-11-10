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

/*
 * Outputs in DOT graph format. Can be layed out by the dotty/neato tools.
 */

namespace printer
{

using std::string;
using std::endl;
using namespace BEEV;

void outputBitVec(const ASTNode n, ostream& os);

void Dot_Print1(ostream& os, const ASTNode n, hash_set<int>* alreadyOutput)
{

  // check if this node has already been printed. If so return.
  if (alreadyOutput->find(n.GetNodeNum()) != alreadyOutput->end())
    return;

  alreadyOutput->insert(n.GetNodeNum());

  os << "n" << n.GetNodeNum() << "[label =\"";
  switch (n.GetKind())
  {
    case SYMBOL:
      n.nodeprint(os);
      break;

    case BITVECTOR:
    case BVCONST:
      outputBitVec(n, os);
      break;

    default:
      os << _kind_names[n.GetKind()];
  }

  os << "\"];" << endl;

  // print the edges to each child.
  ASTVec ch = n.GetChildren();
  ASTVec::iterator itend = ch.end();
  int i = 0;
  for (ASTVec::iterator it = ch.begin(); it < itend; it++)
  {
    os << "n" << n.GetNodeNum() << " -> "
       << "n" << it->GetNodeNum() << "[label=" << i++ << "];" << endl;
  }

  // print each of the children.
  for (ASTVec::iterator it = ch.begin(); it < itend; it++)
  {
    Dot_Print1(os, *it, alreadyOutput);
  }
}

ostream& Dot_Print(ostream& os, const ASTNode n)
{

  os << "digraph G{" << endl;

  // create hashmap to hold integers (node numbers).
  hash_set<int> alreadyOutput;

  Dot_Print1(os, n, &alreadyOutput);

  os << "}" << endl;

  return os;
}
}

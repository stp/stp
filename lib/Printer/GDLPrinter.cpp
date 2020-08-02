// Outputs in the Graph Description Langauge format (GDL)
// can be laid out by the graph layout tool: aiSee.

// todo: this contains only small differences to the dotprinter.cpp. they should
// be merged.

/********************************************************************
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
#include <string>

namespace printer
{

using std::string;
using std::endl;
using namespace stp;

void outputBitVec(const ASTNode n, ostream& os);

void GDL_Print1(ostream& os, const ASTNode& n,
                std::unordered_set<int>* alreadyOutput,
                string (*annotate)(const ASTNode&))
{
  // check if this node has already been printed. If so return.
  if (alreadyOutput->find(n.GetNodeNum()) != alreadyOutput->end())
    return;

  alreadyOutput->insert(n.GetNodeNum());

  os << "node: { title:\"n" << n.GetNodeNum() << "\" label: \"";
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

  os << annotate(n);
  os << "\"}" << endl;

  // print the edges to each child.
  const ASTVec ch = n.GetChildren();
  const ASTVec::const_iterator itend = ch.end();

  // If a node has the child 'TRUE' twice, we only want to output one TRUE node.
  ASTNodeSet constantOutput;

  int i = 0;
  for (ASTVec::const_iterator it = ch.begin(); it < itend; it++)
  {
    std::stringstream label;

    if (!isCommutative(n.GetKind()))
      label << " label:\"" << i << "\"";

    if (it->isConstant())
    {
      std::stringstream ss;
      ss << n.GetNodeNum() << "_" << it->GetNodeNum();

      if (constantOutput.end() == constantOutput.find(*it))
      {
        os << "node: { title:\"n";

        os << ss.str() << "\" label: \"";
        if (it->GetType() == stp::BOOLEAN_TYPE)
          os << _kind_names[it->GetKind()];
        else
          outputBitVec(*it, os);
        os << "\"}" << endl;
        constantOutput.insert(*it);
      }

      os << "edge: { source:\"n" << n.GetNodeNum() << "\" target: \""
         << "n" << ss.str() << "\"" << label.str() << "}" << endl;
    }
    else
      os << "edge: { source:\"n" << n.GetNodeNum() << "\" target: \""
         << "n" << it->GetNodeNum() << "\"" << label.str() << "}" << endl;
    i++;
  }

  // print each of the children.
  for (ASTVec::const_iterator it = ch.begin(); it < itend; it++)
  {
    if (!it->isConstant())
      GDL_Print1(os, *it, alreadyOutput, annotate);
  }
}

string empty(const ASTNode& /*n*/)
{
  return "";
}

ostream& GDL_Print(ostream& os, const ASTNode n,
                   string (*annotate)(const ASTNode&))
{

  os << "graph: {" << endl;
  os << "splines: yes" << endl;
  os << "layoutalgorithm: dfs" << endl;
  os << "display_edge_labels: yes" << endl;

  // create hashmap to hold integers (node numbers).
  std::unordered_set<int> alreadyOutput;

  GDL_Print1(os, n, &alreadyOutput, annotate);
  ;

  os << "}" << endl;

  return os;
}

ostream& GDL_Print(ostream& os, const ASTNode n)
{
  return GDL_Print(os, n, empty);
}
}
